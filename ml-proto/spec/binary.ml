exception Decoding of int * string


let error pos msg = raise (Decoding (i, msg))
let require b pos msg = if not b then error pos msg


(* Decoding stream *)

type stream =
{
  bytes : bytes;
  mutable pos : int;
  limit : int;
}

let stream b = {bytes = b; pos = 0; len = Bytes.length b}
let substream s len = {s with len = s.pos + len}
let len s = s.len
let pos s = s.pos
let eos s = (pos s = len s)

let bytes s pos len =
  require (Bytes.length s.bytes >= pos + len) (pos s) "segment out of bounds";
  Bytes.sub s.bytes pos len

let string s pos =
  (*TODO: leb128?*)
  require (Bytes.length s.bytes > pos) (pos s) "string out of bounds";
  let end =
    try Bytes.index_from s.bytes pos '\x00' with Not_found ->
      error pos "unterminated string"
  in Bytes.sub_string s.bytes pos (end - pos)

let check s = require not (eos s) (len s) "unexpected end of binary"
let peek s = check s; Bytes.get s.bytes s.pos
let adv s = check s; s.pos <- s.pos + 1
let rew s = s.pos <- s.pos - 1
let get s = check s; let i = s.pos in s.pos <- i + 1; Bytes.get s.bytes i

let repeat n f s = if n = 0 then [] else let x = f s in x :: repeat (n - 1) f s


(* Decode section header *)

let decode_section_header s =
  match get s with
  | '\x00' -> `MemorySection
  | '\x01' -> `TypesSection
  | '\x02' -> `FuncsSection
  | '\x03' -> error (pos s - 1) "illegal globals section"
  | '\x04' -> `DataSection
  | '\x05' -> `TableSection
  | '\x06' -> `EndSection
  | _ -> error (pos s - 1) "invalid section code"


(* Decode immediates and markers *)

let expect b s msg = require (get s = b) (pos s - 1) msg
let illegal s =
  rew s; error (pos s) ("Illegal opcode " ^ string_of_int (Char.chr (peek s)))

let u8 s = Char.code (get s)
let bool8 s = u8 s <> 0

let u16 s =
  let lo = u8 s in
  let hi = u8 s in
  256 * hi + lo

let u32 s =
  let lo = Int32.of_int (u16 s) in
  let hi = Int32.of_int (u16 s) in
  Int32.(65536l * hi + lo)

let leb128 s =
  let b = u8 s in
  let x = Int32.of_int (b & 0x7f) in
  if b & 0x80 = 0 then x else Int32.(logor x (shift_left (leb128 s) 7))
  (*TODO: check for overflow*)

let bit i n = n & (1 lsl i) <> 0


(* Decode types *)

let decode_value_type s =
  let open Types in
  match get s with
  | '\x01' -> Int32Type
  | '\x02' -> Int64type
  | '\x03' -> Float32Type
  | '\x04' -> Float64Type
  | _ -> error (pos s - 1) "invalid value type"

let decode_expr_type s =
  match peek s with
  | '\x00' -> adv s; None
  | _ -> Some (decode_value_type s)

let decode_func_type s =
  let arity = u8 s in
  let out = decode_expr_type s in
  let ins = repeat arity decode_value_type s i
  {ins; out}


(* Decode expressions *)

let decode_memop s =
  let flags = u8 s in
  let offset = if bit 4 flags then leb128 s else 0 in
  let align = bit 7 flags in  (*TODO*)
  offset, align

let opt e = if e.it = Nop then None else Some e

let rec decode_expr_block s =
  List.rev (decode_exprs s [])

and decode_exprs s stack =
  let i = pos s in
  let stack' = decode_expr s stack in
  if pos s = i then stack' else decode_exprs s stack'

and decode_expr s stack =
  let open Ast in
  if eos s then stack else
  match get s, stack with
  | '\x00', es ->
    Nop :: es
  | '\x01', es ->
    let es' = decode_expr_block s in
    expect '\x17' "end opcode expected";
    Block es' :: es
  | '\x02', es ->
    let es' = decode_expr_block s in
    expect '\x17' "end opcode expected";
    Loop es' :: es
  | '\x03', e :: es ->
    let es1 = decode_expr_block s in
    if peek s = '\x04' then begin
      expect '\x04' "else or end opcode expected";
      let es2 = decode_expr_block s in
      expect '\x17' "end opcode expected";
      If_else (e, es1, es2) (*TODO: separate opcode?*)
    end else begin
      expect '\x17' "end opcode expected";
      If (e, es1)
    end
  | '\x04', es ->
    rew s; es (* next *)
  | '\x05', e3 :: e2 :: e1 :: es ->
    Select (e1, e2, e3) :: es
  | '\x06', e :: es ->
    let x = u8 s in
    Br (x, opt e) :: es
  | '\x07', e2 :: e1 :: es ->
    let x = u8 s in
    Br_if (x, opt e1, e2)
  | '\x08', e :: es ->
    let len_cases = u16 s in
    let len_targets = u16 s in  (*TODO: minus 1?*)
    require (len_targets = 0) (pos s - 2) "empty switch table";
    let ts = repeat (len_targets - 1) decode_target s in
    let t = decode_target s in
    let e = decode_expr s in
    let es = repeat len_cases decode_expr s in
    Tableswitch (e, ts, t, List.map (fun e -> [e]) es) (*TODO: fix AST*)

  | '\x09', es -> I32_const (Int32.of_int (u8 s) & 0xffl) :: es (*TODO: opcode?*)
  | '\x0a', es -> I32_const (u32 s) :: es
  | '\x0b', es -> I64_const (u64 s) :: es
  | '\x0c', es -> F32_const (f32 s) :: es
  | '\x0d', es -> F64_const (f64 s) :: es

  | '\x0e', es ->
    let x = leb128 s in
    Get_local x :: es
  | '\x0f', e :: es ->
    let x = leb128 s in
    Set_local (x, e) :: es
  | '\x10', _ -> illegal s (* get_global *)
  | '\x11', _ -> illegal s (* set_global *)

  | '\x12', es ->
    let x = leb128 s in
    let arity = (*TODO: from func table*) in
    let es' = pop s arity in
    Call (x, es') :: s.stack
  | '\x13', e es ->
    let x = leb128 s in
    let arity = (*TODO: from type table*) in
    let e = decode_expr s in
    let es' = pop s arity in
    Call_indirect (x, e, es')
  (*TODO: Call_import?*)

  | '\x14', es ->
    let arity = (*TODO: from func table*) in
    let eo = if arity = 0 then None else Some (pop s 1) in
    Return eo :: s.stack
  | '\x15', es ->
    Unreachable :: es

  | '\x16', es ->
    rew s; es (* next *)
  | '\x17', es ->
    rew s; es (* end *)

  | '\x18'..'\x1f' -> illegal s

  | '\x20', e :: es -> I32_load8_s (0, None, e) :: es
  | '\x21', e :: es -> I32_load8_u (0, None, e) :: es
  | '\x22', e :: es -> I32_load16_s (0, None, e) :: es
  | '\x23', e :: es -> I32_load16_u (0, None, e) :: es
  | '\x24', e :: es -> I64_load8_s (0, None, e) :: es
  | '\x25', e :: es -> I64_load8_u (0, None, e) :: es
  | '\x26', e :: es -> I64_load16_s (0, None, e) :: es
  | '\x27', e :: es -> I64_load16_u (0, None, e) :: es
  | '\x28', e :: es -> I64_load32_s (0, None, e) :: es
  | '\x29', e :: es -> I64_load32_u (0, None, e) :: es
  | '\x2a', e :: es -> I32_load (0, None, e) :: es
  | '\x2b', e :: es -> I64_load (0, None, e) :: es
  | '\x2c', e :: es -> F32_load (0, None, e) :: es
  | '\x2d', e :: es -> F64_load (0, None, e) :: es

  | '\x2e', e2 :: e1 :: es -> I32_store8 (0, None, e1, e2) :: es
  | '\x2f', e2 :: e1 :: es -> I32_store16 (0, None, e1, e2) :: es
  | '\x30', e2 :: e1 :: es -> I64_store8 (0, None, e1, e2) :: es
  | '\x31', e2 :: e1 :: es -> I64_store16 (0, None, e1, e2) :: es
  | '\x32', e2 :: e1 :: es -> I64_store32 (0, None, e1, e2) :: es
  | '\x33', e2 :: e1 :: es -> I32_store (0, None, e1, e2) :: es
  | '\x34', e2 :: e1 :: es -> I64_store (0, None, e1, e2) :: es
  | '\x35', e2 :: e1 :: es -> F32_store (0, None, e1, e2) :: es
  | '\x36', e2 :: e1 :: es -> F64_store (0, None, e1, e2) :: es

  | '\x37'..'\x38', _ -> illegal s
  | '\x39', e :: es -> Grow_memory e :: es
  | '\x3a', _ -> illegal s
  | '\x3b', es -> Memory_size :: es

  | '\x40', e2 :: e1 :: es -> I32_add (e1, e2) :: es
  | '\x41', e2 :: e1 :: es -> I32_sub (e1, e2) :: es
  | '\x42', e2 :: e1 :: es -> I32_mul (e1, e2) :: es
  | '\x43', e2 :: e1 :: es -> I32_div_s (e1, e2) :: es
  | '\x44', e2 :: e1 :: es -> I32_div_u (e1, e2) :: es
  | '\x45', e2 :: e1 :: es -> I32_rem_s (e1, e2) :: es
  | '\x46', e2 :: e1 :: es -> I32_rem_u (e1, e2) :: es
  | '\x47', e2 :: e1 :: es -> I32_and (e1, e2) :: es
  | '\x48', e2 :: e1 :: es -> I32_or (e1, e2) :: es
  | '\x49', e2 :: e1 :: es -> I32_xor (e1, e2) :: es
  | '\x4a', e2 :: e1 :: es -> I32_shl (e1, e2) :: es
  | '\x4b', e2 :: e1 :: es -> I32_shr_u (e1, e2) :: es
  | '\x4c', e2 :: e1 :: es -> I32_shr_s (e1, e2) :: es
  | '\x4d', e2 :: e1 :: es -> I32_eq (e1, e2) :: es
  | '\x4e', e2 :: e1 :: es -> I32_ne (e1, e2) :: es
  | '\x4f', e2 :: e1 :: es -> I32_lt_s (e1, e2) :: es
  | '\x50', e2 :: e1 :: es -> I32_le_s (e1, e2) :: es
  | '\x51', e2 :: e1 :: es -> I32_lt_u (e1, e2) :: es
  | '\x52', e2 :: e1 :: es -> I32_le_u (e1, e2) :: es
  | '\x53', e2 :: e1 :: es -> I32_gt_s (e1, e2) :: es
  | '\x54', e2 :: e1 :: es -> I32_ge_s (e1, e2) :: es
  | '\x55', e2 :: e1 :: es -> I32_gt_u (e1, e2) :: es
  | '\x56', e2 :: e1 :: es -> I32_ge_u (e1, e2) :: es
  | '\x57', e :: es -> I32_clz e :: es
  | '\x58', e :: es -> I32_ctz e :: es
  | '\x59', e :: es -> I32_popcnt e :: es
  | '\x5a', e :: es -> I32_not e :: es (*TODO*)

  | '\x5b', e2 :: e1 :: es -> I64_add (e1, e2) :: es
  | '\x5c', e2 :: e1 :: es -> I64_sub (e1, e2) :: es
  | '\x5d', e2 :: e1 :: es -> I64_mul (e1, e2) :: es
  | '\x5e', e2 :: e1 :: es -> I64_div_s (e1, e2) :: es
  | '\x5f', e2 :: e1 :: es -> I64_div_u (e1, e2) :: es
  | '\x60', e2 :: e1 :: es -> I64_rem_s (e1, e2) :: es
  | '\x61', e2 :: e1 :: es -> I64_rem_u (e1, e2) :: es
  | '\x62', e2 :: e1 :: es -> I64_and (e1, e2) :: es
  | '\x63', e2 :: e1 :: es -> I64_or (e1, e2) :: es
  | '\x64', e2 :: e1 :: es -> I64_xor (e1, e2) :: es
  | '\x65', e2 :: e1 :: es -> I64_shl (e1, e2) :: es
  | '\x66', e2 :: e1 :: es -> I64_shr_u (e1, e2) :: es
  | '\x67', e2 :: e1 :: es -> I64_shr_s (e1, e2) :: es
  | '\x68', e2 :: e1 :: es -> I64_eq (e1, e2) :: es
  | '\x69', e2 :: e1 :: es -> I64_ne (e1, e2) :: es
  | '\x6a', e2 :: e1 :: es -> I64_lt_s (e1, e2) :: es
  | '\x6b', e2 :: e1 :: es -> I64_le_s (e1, e2) :: es
  | '\x6c', e2 :: e1 :: es -> I64_lt_u (e1, e2) :: es
  | '\x6d', e2 :: e1 :: es -> I64_le_u (e1, e2) :: es
  | '\x6e', e2 :: e1 :: es -> I64_gt_s (e1, e2) :: es
  | '\x6f', e2 :: e1 :: es -> I64_ge_s (e1, e2) :: es
  | '\x70', e2 :: e1 :: es -> I64_gt_u (e1, e2) :: es
  | '\x71', e2 :: e1 :: es -> I64_ge_u (e1, e2) :: es
  | '\x72', e :: es -> I64_clz e :: es
  | '\x73', e :: es -> I64_ctz e :: es
  | '\x74', e :: es -> I64_popcnt e :: es

  | '\x75', e2 :: e1 :: es -> F32_add (e1, e2) :: es
  | '\x76', e2 :: e1 :: es -> F32_sub (e1, e2) :: es
  | '\x77', e2 :: e1 :: es -> F32_mul (e1, e2) :: es
  | '\x78', e2 :: e1 :: es -> F32_div (e1, e2) :: es
  | '\x79', e2 :: e1 :: es -> F32_min (e1, e2) :: es
  | '\x7a', e2 :: e1 :: es -> F32_max (e1, e2) :: es
  | '\x7b', e :: es -> F32_abs e :: es
  | '\x7c', e :: es -> F32_neg e :: es
  | '\x7d', e2 :: e1 :: es -> F32_copysign (e1, e2) :: es
  | '\x7e', e :: es -> F32_ceil e :: es
  | '\x7f', e :: es -> F32_floor e :: es
  | '\x80', e :: es -> F32_trunc e :: es
  | '\x81', e :: es -> F32_nearest e :: es
  | '\x82', e :: es -> F32_sqrt e :: es
  | '\x83', e2 :: e1 :: es -> F32_eq (e1, e2) :: es
  | '\x84', e2 :: e1 :: es -> F32_ne (e1, e2) :: es
  | '\x85', e2 :: e1 :: es -> F32_lt (e1, e2) :: es
  | '\x86', e2 :: e1 :: es -> F32_le (e1, e2) :: es
  | '\x87', e2 :: e1 :: es -> F32_gt (e1, e2) :: es
  | '\x88', e2 :: e1 :: es -> F32_ge (e1, e2) :: es

  | '\x89', e2 :: e1 :: es -> F64_add (e1, e2) :: es
  | '\x8a', e2 :: e1 :: es -> F64_sub (e1, e2) :: es
  | '\x8b', e2 :: e1 :: es -> F64_mul (e1, e2) :: es
  | '\x8c', e2 :: e1 :: es -> F64_div (e1, e2) :: es
  | '\x8d', e2 :: e1 :: es -> F64_min (e1, e2) :: es
  | '\x8e', e2 :: e1 :: es -> F64_max (e1, e2) :: es
  | '\x8f', e :: es -> F64_abs e :: es
  | '\x90', e :: es -> F64_neg e :: es
  | '\x91', e2 :: e1 :: es -> F64_copysign (e1, e2) :: es
  | '\x92', e :: es -> F64_ceil e :: es
  | '\x93', e :: es -> F64_floor e :: es
  | '\x94', e :: es -> F64_trunc e :: es
  | '\x95', e :: es -> F64_nearest e :: es
  | '\x96', e :: es -> F64_sqrt e :: es
  | '\x97', e2 :: e1 :: es -> F64_eq (e1, e2) :: es
  | '\x98', e2 :: e1 :: es -> F64_ne (e1, e2) :: es
  | '\x99', e2 :: e1 :: es -> F64_lt (e1, e2) :: es
  | '\x9a', e2 :: e1 :: es -> F64_le (e1, e2) :: es
  | '\x9b', e2 :: e1 :: es -> F64_gt (e1, e2) :: es
  | '\x9c', e2 :: e1 :: es -> F64_ge (e1, e2) :: es

  | '\x9d', e :: es -> I32_trunc_s_f32 e :: es
  | '\x9e', e :: es -> I32_trunc_s_f64 e :: es
  | '\x9f', e :: es -> I32_trunc_u_f32 e :: es
  | '\xa0', e :: es -> I32_trunc_u_f64 e :: es
  | '\xa1', e :: es -> I32_wrap_i64 e ::es
  | '\xa2', e :: es -> I32_trunc_s_f32 e :: es
  | '\xa3', e :: es -> I32_trunc_s_f64 e :: es
  | '\xa4', e :: es -> I32_trunc_u_f32 e :: es
  | '\xa5', e :: es -> I32_trunc_u_f64 e :: es
  | '\xa6', e :: es -> I64_extend_s_i32 e :: es
  | '\xa7', e :: es -> I64_extend_u_i32 e :: es
  | '\xa8', e :: es -> F32_convert_s_i32 e :: es
  | '\xa9', e :: es -> F32_convert_u_i32 e :: es
  | '\xaa', e :: es -> F32_convert_s_i64 e :: es
  | '\xab', e :: es -> F32_convert_u_i64 e :: es
  | '\xac', e :: es -> F32_demote_f64 e :: es
  | '\xad', e :: es -> F32_reinterpret_i32 e :: es
  | '\xae', e :: es -> F64_convert_s_i32 e :: es
  | '\xaf', e :: es -> F64_convert_u_i32 e :: es
  | '\xb0', e :: es -> F64_convert_s_i64 e :: es
  | '\xb1', e :: es -> F64_convert_u_i64 e :: es
  | '\xb2', e :: es -> F64_promote_f32 e :: es
  | '\xb3', e :: es -> F64_reinterpret_i64 e :: es
  | '\xb4', e :: es -> I32_reinterpret_f32 e :: es
  | '\xb5', e :: es -> I64_reinterpret_f64 e :: es

  | '\xb6'..'\xff', _ -> illegal s

  | _ -> error (pos s) "unexpected end of function"

and decode_target s in
  let x = u16 s in
  if x & 0x8000 = 0 then
    Case x
  else
    Case_br (x & 0x7fff)


(* Decode memory section *)

let decode_power_of_2 s =
  let n = u8 s in
  require (n < 64) (pos s - 1) "shift value out of range";
  Int64.(shift_left 1L (of_int n))

let decode_memory s =
  if decode_section_header s <> `MemorySection then None else
  let initial = decode_power_of_2 s in
  let max = decode_power_of_2 s in
  let exported = bool8 s in (*TODO: spec has name*)
  Some (initial, max)


(* Decode type section *)

let decode_types s =
  if decode_section_header s <> `TypesSection then [] else
  let len = leb128 s in
  let types = repeat len decode_func_type s in
  types


(* Decode function section *)

let decode_locals s =
  (*TODO: improve this format?*)
  let i32_len = u16 s in
  let i64_len = u16 s in
  let f32_len = u16 s in
  let f64_len = u16 s in
  make i32_len Int32Type @ make i64_len Int64Type @
  make f32_len Float32Type @ make f64_len Float64Type

let decode_body s =
  let size = u16 s in (*TODO: leb128?*)
  let pos1 = pos s in
  let expr = decode_expr s in (*TODO: no list?*)
  let pos2 = pos s in
  if pos1 + size <> pos2 then error (pos1 - 2) "incorrect body size";
  [expr]

let decode_name s =
  let pos = u32 s in
  decode_string s pos

let decode_func s =
  let ftype = u16 s in
  let flags = u8 s in (*TODO: validate*)
  let has_name = bit 0 flags in
  let imported = bit 1 flags in
  let has_locals = bit 2 flags in
  let exported = bit 3 flags in
  require (has_name || not imported && not exported)
    (pos s - 1) "unnamed import or export";
  let name = if has_name then Some (decode_name s) else None in
  let locals = if has_locals then decode_locals s else [] in
  let body = if not imported then Ast.Nop else decode_body s in
  if imported then
    (*TODO: import module name?*)
    `Import {Kernel.itype = ftype; module_name = ""; func_name = name}
  else
  let func = {ftype; locals; body} in
  if exported then
    `Export (func, name)
  else
    `Internal func

(*TODO: function indexing?*)
let rec separate funcs imports exports = function
  | [] -> List.rev funcs, List.rev imports, List.rev exports
  | `Internal func -> separate (func::funcs) imports exports
  | `Import import -> separate funcs (import::imports) exports
  | `Export (func, name) ->
    let export = {Kernel.name = name; func = List.length funcs} in
    separate (func::funcs) imports (export::exports)

let decode_funcs s =
  if decode_section_header s <> `FuncsSection then [], [], [] else
  let len = leb128 s in
  let pos = 
  let entries = repeat len decode_func s in
  separate [] [] [] entries


(* Decode data *)

let decode_segment s =
  let addr = Int64.of_int32 (u32 s) logand 0xffffffffL in
  let offset = u32 s in
  let size = u32 s in
  let init = bool8 s in (*TODO: unused*)
  let data = bytes s offset size in
  {addr; data}

let decode_data s =
  if decode_section_header s <> `DataSection then [] else
  let len = leb128 s in
  let segments = repeat len decode_segment s in
  segments


(* Decode table *)

let decode_table s =
  if decode_section_header s <> `TableSection then [] else
  let len = leb128 s in
  let table = repeat len u16 s in
  table


(* Decode module *)

let decode_end s =
  if decode_section_header s <> `EndSection then
    error (pos s - 1) "misplaced or duplicate section"

let decode_module s =
  let mem = decode_memory s in
  let types = decode_types s in
  let funcs, imports, exports = decode_funcs s in
  let segments = decode_data s in (*TODO: merge with memory*)
  let table = decode_table s in
  let () = decode_end s in
  let memory =
    match mem with
    | None when segments = [] -> None
    | None -> error 0 "segment section without data section"
    | Some (initial, max) -> Some {initial; max; segments}
  in {memory; types; funcs; imports; exports; table}

let binary_to_module b = decode_module (stream b)
