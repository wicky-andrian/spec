(* Errors *)

module Decoding = Error.Make ()
exception Decoding = Decoding.Error


(* Decoding stream *)

type stream =
{
  name : string;
  bytes : bytes;
  pos : int ref;
  len : int;
}

let stream name b = {name; bytes = b; pos = ref 0; len = Bytes.length b}
let substream s len = {s with len = !(s.pos) + len}
let len s = s.len
let pos s = !(s.pos)
let eos s = (pos s = len s)


let position s pos = Source.({file = s.name; line = -1; column = pos})
let region s pos =
  let position = position s pos in
  Source.({left = position; right = position})

let error s pos msg = raise (Decoding (region s pos, msg))
let require b s pos msg = if not b then error s pos msg

let string_of_byte b = Printf.sprintf "%02x" (Char.code b)


let bytes s off len =
  require (Int32.of_int (Bytes.length s.bytes) >= Int32.add off len)
    s (pos s) "segment out of bounds";
  Bytes.sub s.bytes (Int32.to_int off) (Int32.to_int len)

let string s off =
  (*TODO: leb128?*)
  require (Int32.of_int (Bytes.length s.bytes) > off)
    s (pos s) "string out of bounds";
  let bos = Int32.to_int off in
  let eos =
    try Bytes.index_from s.bytes bos '\x00' with Not_found ->
      error s bos "unterminated string"
  in Bytes.sub_string s.bytes bos (eos - bos)

let check s =
  require (not (eos s)) s (len s) "unexpected end of binary or function"

let peek s = check s; Bytes.get s.bytes !(s.pos)
let adv s = check s; s.pos := !(s.pos) + 1
let get s = check s; let i = !(s.pos) in s.pos := i + 1; Bytes.get s.bytes i

let rec repeat n f s =
  if n = 0l then [] else let x = f s in x :: repeat (Int32.sub n 1l) f s

let at decode_fn s =
  let left = pos s in
  let x = decode_fn s in
  let right = pos s in
  Source.(x @@ {left = position s left; right = position s right})


(* Decode immediates and markers *)

let expect b s msg = require (get s = b) s (pos s - 1) msg
let illegal s pos b = error s pos ("Illegal opcode " ^ string_of_byte b)

let bit i n = n land (1 lsl i) <> 0

let u8 s = Char.code (get s)
let bool8 s = u8 s <> 0

let u16 s =
  let lo = u8 s in
  let hi = u8 s in
  256 * hi + lo

let u32 s =
  let lo = Int32.of_int (u16 s) in
  let hi = Int32.of_int (u16 s) in
  Int32.(add lo (mul 65536l hi))

let rec leb128 s =
  let b = u8 s in
  let x = Int32.of_int (b land 0x7f) in
  if b land 0x80 = 0 then x else Int32.(logor x (shift_left (leb128 s) 7))
  (*TODO: check for overflow*)


(* Decode section header *)

let decode_section_header s =
  match get s with (*TODO: reorder?*)
  | '\x00' -> `MemorySection
  | '\x01' -> `TypeSection
  | '\x02' -> `FuncSection
  | '\x03' -> error s (pos s - 1) "illegal globals section"
  | '\x04' -> `DataSection
  | '\x05' -> `TableSection
  | '\x06' -> `EndSection
  | '\x08' -> `ImportSection
  | '\x09' -> `ExportSection
  | b -> error s (pos s - 1) ("invalid section code" ^ string_of_byte b)


(* Leafs and vectors *)

let decode_name s =
  let off = u32 s in
  string s off

let decode_var s =
  u16 s

let decode_vec decode_fn s =
  let len = leb128 s in
  repeat len decode_fn s


(* Decode types *)

let decode_value_type s =
  let open Types in
  match get s with
  | '\x01' -> Int32Type
  | '\x02' -> Int64Type
  | '\x03' -> Float32Type
  | '\x04' -> Float64Type
  | _ -> error s (pos s - 1) "invalid value type"

let decode_expr_type s =
  match peek s with
  | '\x00' -> adv s; None
  | _ -> Some (decode_value_type s)

let decode_func_type s = (*TODO: no marker?*)
  let arity = Int32.of_int (u8 s) in
  let out = decode_expr_type s in
  let ins = repeat arity decode_value_type s in
  Types.({ins; out})


(* Decode expressions *)

let decode_memop s =
  let flags = u8 s in
  let offset = if bit 4 flags then leb128 s else 0l in
  let align = bit 7 flags in  (*TODO*)
  offset, align

let opt e = if e.Source.it = Ast.Nop then None else Some e

let rec decode_expr_block s =
  List.rev (decode_exprs s [])

and decode_exprs s stack =
  let i = pos s in
  let stack' = decode_expr s stack in
  if pos s = i then stack' else decode_exprs s stack'

and decode_expr s stack =
  if eos s then stack else
  match peek s with
  | '\x04' | '\x16' | '\x17' -> stack
  | _ ->
    let reg = region s (pos s) in
    let e', stack' = decode_op s stack in
    Source.(e' @@ reg) :: stack'

and decode_op s stack =
  let open Ast in
  match get s, stack with
  | '\x00', es ->
    Nop, es
  | '\x01', es ->
    let es' = decode_expr_block s in
    expect '\x17' s "end opcode expected";
    Block es', es
  | '\x02', es ->
    let es' = decode_expr_block s in
    expect '\x17' s "end opcode expected";
    Loop es', es
  | '\x03', e :: es ->
    let es1 = decode_expr_block s in
    if peek s = '\x04' then begin
      expect '\x04' s "else or end opcode expected";
      let es2 = decode_expr_block s in
      expect '\x17' s "end opcode expected";
      If_else (e, es1, es2), es (*TODO: separate opcode?*)
    end else begin
      expect '\x17' s "end opcode expected";
      If (e, es1), es
    end
  | '\x04', _ ->
    assert false (* else *)
  | '\x05', e3 :: e2 :: e1 :: es ->
    (*TODO: make Select parametric *)
    Nop (*Select (e1, e2, e3)*), es
  | '\x06', e :: es ->
    let x = at decode_var s in
    Br (x, opt e), es
  | '\x07', e2 :: e1 :: es ->
    let x = at decode_var s in
    Br_if (x, opt e1, e2), es
  | '\x08', e :: es ->
illegal s (pos s - 1) '\x08' (*TODO
    let len_cases = u16 s in
    let len_targets = u16 s in  (*TODO: minus 1?*)
    require (len_targets = 0) s (pos s - 2) "empty switch table";
    let ts = repeat (len_targets - 1) (at decode_target) s in
    let t = at decode_target s in
    let es = repeat len_cases decode_expr s in
    Tableswitch (e, ts, t, List.map (fun e -> [e]) es) (*TODO: fix AST*)
*)

  | '\x09', es -> I32_const (Int32.of_int (u8 s) & 0xffl), es (*TODO: opcode?*)
  | '\x0a', es -> I32_const (u32 s), es
  | '\x0b', es -> I64_const (u64 s), es
  | '\x0c', es -> F32_const (f32 s), es
  | '\x0d', es -> F64_const (f64 s), es

  | '\x0e', es ->
    let x = at decode_var s in
    Get_local x, es
  | '\x0f', e :: es ->
    let x = at decode_var s in
    Set_local (x, e), es
  | '\x10' | '\x11' as b, _ ->
    illegal s (pos s - 1) b (* get/set_global *)

  | '\x12', es ->
    let x = leb128 s in (*TODO: var*)
    let arity = 1 (*TODO: from func table*) in
    Call (x, Lib.List. take arity es), Lib.List.drop arity es
  | '\x13', e :: es ->
    let x = leb128 s in (*TODO: var*)
    let arity = 1 (*TODO: from type table*) in
    Call_indirect (x, e, Lib.List. take arity es), Lib.List.drop arity es
  (*TODO: Call_import?*)

  | '\x14', es ->
    let arity = 1 (*TODO: from func table*) in
    let eo = if arity = 0 then None else Some (pop s 1) in
    Return eo, s.stack
  | '\x15', es ->
    Unreachable, es

  | '\x16', _ -> assert false (* next *)
  | '\x17', _ -> assert false (* end *)
  | '\x18'..'\x1f' as b, _ -> illegal s (pos s - 1) b

  | '\x20', e :: es -> I32_load8_s (0, None, e), es
  | '\x21', e :: es -> I32_load8_u (0, None, e), es
  | '\x22', e :: es -> I32_load16_s (0, None, e), es
  | '\x23', e :: es -> I32_load16_u (0, None, e), es
  | '\x24', e :: es -> I64_load8_s (0, None, e), es
  | '\x25', e :: es -> I64_load8_u (0, None, e), es
  | '\x26', e :: es -> I64_load16_s (0, None, e), es
  | '\x27', e :: es -> I64_load16_u (0, None, e), es
  | '\x28', e :: es -> I64_load32_s (0, None, e), es
  | '\x29', e :: es -> I64_load32_u (0, None, e), es
  | '\x2a', e :: es -> I32_load (0, None, e), es
  | '\x2b', e :: es -> I64_load (0, None, e), es
  | '\x2c', e :: es -> F32_load (0, None, e), es
  | '\x2d', e :: es -> F64_load (0, None, e), es

  | '\x2e', e2 :: e1 :: es -> I32_store8 (0, None, e1, e2), es
  | '\x2f', e2 :: e1 :: es -> I32_store16 (0, None, e1, e2), es
  | '\x30', e2 :: e1 :: es -> I64_store8 (0, None, e1, e2), es
  | '\x31', e2 :: e1 :: es -> I64_store16 (0, None, e1, e2), es
  | '\x32', e2 :: e1 :: es -> I64_store32 (0, None, e1, e2), es
  | '\x33', e2 :: e1 :: es -> I32_store (0, None, e1, e2), es
  | '\x34', e2 :: e1 :: es -> I64_store (0, None, e1, e2), es
  | '\x35', e2 :: e1 :: es -> F32_store (0, None, e1, e2), es
  | '\x36', e2 :: e1 :: es -> F64_store (0, None, e1, e2), es

  | '\x37'..'\x38' as b, _ -> illegal s (pos s - 1) b
  | '\x39', e :: es -> Grow_memory e, es
  | '\x3a' as b, _ -> illegal s (pos s - 1) b
  | '\x3b', es -> Memory_size, es

  | '\x40', e2 :: e1 :: es -> I32_add (e1, e2), es
  | '\x41', e2 :: e1 :: es -> I32_sub (e1, e2), es
  | '\x42', e2 :: e1 :: es -> I32_mul (e1, e2), es
  | '\x43', e2 :: e1 :: es -> I32_div_s (e1, e2), es
  | '\x44', e2 :: e1 :: es -> I32_div_u (e1, e2), es
  | '\x45', e2 :: e1 :: es -> I32_rem_s (e1, e2), es
  | '\x46', e2 :: e1 :: es -> I32_rem_u (e1, e2), es
  | '\x47', e2 :: e1 :: es -> I32_and (e1, e2), es
  | '\x48', e2 :: e1 :: es -> I32_or (e1, e2), es
  | '\x49', e2 :: e1 :: es -> I32_xor (e1, e2), es
  | '\x4a', e2 :: e1 :: es -> I32_shl (e1, e2), es
  | '\x4b', e2 :: e1 :: es -> I32_shr_u (e1, e2), es
  | '\x4c', e2 :: e1 :: es -> I32_shr_s (e1, e2), es
  | '\x4d', e2 :: e1 :: es -> I32_eq (e1, e2), es
  | '\x4e', e2 :: e1 :: es -> I32_ne (e1, e2), es
  | '\x4f', e2 :: e1 :: es -> I32_lt_s (e1, e2), es
  | '\x50', e2 :: e1 :: es -> I32_le_s (e1, e2), es
  | '\x51', e2 :: e1 :: es -> I32_lt_u (e1, e2), es
  | '\x52', e2 :: e1 :: es -> I32_le_u (e1, e2), es
  | '\x53', e2 :: e1 :: es -> I32_gt_s (e1, e2), es
  | '\x54', e2 :: e1 :: es -> I32_ge_s (e1, e2), es
  | '\x55', e2 :: e1 :: es -> I32_gt_u (e1, e2), es
  | '\x56', e2 :: e1 :: es -> I32_ge_u (e1, e2), es
  | '\x57', e :: es -> I32_clz e, es
  | '\x58', e :: es -> I32_ctz e, es
  | '\x59', e :: es -> I32_popcnt e, es
  | '\x5a', e :: es -> I32_not e, es (*TODO*)

  | '\x5b', e2 :: e1 :: es -> I64_add (e1, e2), es
  | '\x5c', e2 :: e1 :: es -> I64_sub (e1, e2), es
  | '\x5d', e2 :: e1 :: es -> I64_mul (e1, e2), es
  | '\x5e', e2 :: e1 :: es -> I64_div_s (e1, e2), es
  | '\x5f', e2 :: e1 :: es -> I64_div_u (e1, e2), es
  | '\x60', e2 :: e1 :: es -> I64_rem_s (e1, e2), es
  | '\x61', e2 :: e1 :: es -> I64_rem_u (e1, e2), es
  | '\x62', e2 :: e1 :: es -> I64_and (e1, e2), es
  | '\x63', e2 :: e1 :: es -> I64_or (e1, e2), es
  | '\x64', e2 :: e1 :: es -> I64_xor (e1, e2), es
  | '\x65', e2 :: e1 :: es -> I64_shl (e1, e2), es
  | '\x66', e2 :: e1 :: es -> I64_shr_u (e1, e2), es
  | '\x67', e2 :: e1 :: es -> I64_shr_s (e1, e2), es
  | '\x68', e2 :: e1 :: es -> I64_eq (e1, e2), es
  | '\x69', e2 :: e1 :: es -> I64_ne (e1, e2), es
  | '\x6a', e2 :: e1 :: es -> I64_lt_s (e1, e2), es
  | '\x6b', e2 :: e1 :: es -> I64_le_s (e1, e2), es
  | '\x6c', e2 :: e1 :: es -> I64_lt_u (e1, e2), es
  | '\x6d', e2 :: e1 :: es -> I64_le_u (e1, e2), es
  | '\x6e', e2 :: e1 :: es -> I64_gt_s (e1, e2), es
  | '\x6f', e2 :: e1 :: es -> I64_ge_s (e1, e2), es
  | '\x70', e2 :: e1 :: es -> I64_gt_u (e1, e2), es
  | '\x71', e2 :: e1 :: es -> I64_ge_u (e1, e2), es
  | '\x72', e :: es -> I64_clz e, es
  | '\x73', e :: es -> I64_ctz e, es
  | '\x74', e :: es -> I64_popcnt e, es

  | '\x75', e2 :: e1 :: es -> F32_add (e1, e2), es
  | '\x76', e2 :: e1 :: es -> F32_sub (e1, e2), es
  | '\x77', e2 :: e1 :: es -> F32_mul (e1, e2), es
  | '\x78', e2 :: e1 :: es -> F32_div (e1, e2), es
  | '\x79', e2 :: e1 :: es -> F32_min (e1, e2), es
  | '\x7a', e2 :: e1 :: es -> F32_max (e1, e2), es
  | '\x7b', e :: es -> F32_abs e, es
  | '\x7c', e :: es -> F32_neg e, es
  | '\x7d', e2 :: e1 :: es -> F32_copysign (e1, e2), es
  | '\x7e', e :: es -> F32_ceil e, es
  | '\x7f', e :: es -> F32_floor e, es
  | '\x80', e :: es -> F32_trunc e, es
  | '\x81', e :: es -> F32_nearest e, es
  | '\x82', e :: es -> F32_sqrt e, es
  | '\x83', e2 :: e1 :: es -> F32_eq (e1, e2), es
  | '\x84', e2 :: e1 :: es -> F32_ne (e1, e2), es
  | '\x85', e2 :: e1 :: es -> F32_lt (e1, e2), es
  | '\x86', e2 :: e1 :: es -> F32_le (e1, e2), es
  | '\x87', e2 :: e1 :: es -> F32_gt (e1, e2), es
  | '\x88', e2 :: e1 :: es -> F32_ge (e1, e2), es

  | '\x89', e2 :: e1 :: es -> F64_add (e1, e2), es
  | '\x8a', e2 :: e1 :: es -> F64_sub (e1, e2), es
  | '\x8b', e2 :: e1 :: es -> F64_mul (e1, e2), es
  | '\x8c', e2 :: e1 :: es -> F64_div (e1, e2), es
  | '\x8d', e2 :: e1 :: es -> F64_min (e1, e2), es
  | '\x8e', e2 :: e1 :: es -> F64_max (e1, e2), es
  | '\x8f', e :: es -> F64_abs e, es
  | '\x90', e :: es -> F64_neg e, es
  | '\x91', e2 :: e1 :: es -> F64_copysign (e1, e2), es
  | '\x92', e :: es -> F64_ceil e, es
  | '\x93', e :: es -> F64_floor e, es
  | '\x94', e :: es -> F64_trunc e, es
  | '\x95', e :: es -> F64_nearest e, es
  | '\x96', e :: es -> F64_sqrt e, es
  | '\x97', e2 :: e1 :: es -> F64_eq (e1, e2), es
  | '\x98', e2 :: e1 :: es -> F64_ne (e1, e2), es
  | '\x99', e2 :: e1 :: es -> F64_lt (e1, e2), es
  | '\x9a', e2 :: e1 :: es -> F64_le (e1, e2), es
  | '\x9b', e2 :: e1 :: es -> F64_gt (e1, e2), es
  | '\x9c', e2 :: e1 :: es -> F64_ge (e1, e2), es

  | '\x9d', e :: es -> I32_trunc_s_f32 e, es
  | '\x9e', e :: es -> I32_trunc_s_f64 e, es
  | '\x9f', e :: es -> I32_trunc_u_f32 e, es
  | '\xa0', e :: es -> I32_trunc_u_f64 e, es
  | '\xa1', e :: es -> I32_wrap_i64 e, es
  | '\xa2', e :: es -> I32_trunc_s_f32 e, es
  | '\xa3', e :: es -> I32_trunc_s_f64 e, es
  | '\xa4', e :: es -> I32_trunc_u_f32 e, es
  | '\xa5', e :: es -> I32_trunc_u_f64 e, es
  | '\xa6', e :: es -> I64_extend_s_i32 e, es
  | '\xa7', e :: es -> I64_extend_u_i32 e, es
  | '\xa8', e :: es -> F32_convert_s_i32 e, es
  | '\xa9', e :: es -> F32_convert_u_i32 e, es
  | '\xaa', e :: es -> F32_convert_s_i64 e, es
  | '\xab', e :: es -> F32_convert_u_i64 e, es
  | '\xac', e :: es -> F32_demote_f64 e, es
  | '\xad', e :: es -> F32_reinterpret_i32 e, es
  | '\xae', e :: es -> F64_convert_s_i32 e, es
  | '\xaf', e :: es -> F64_convert_u_i32 e, es
  | '\xb0', e :: es -> F64_convert_s_i64 e, es
  | '\xb1', e :: es -> F64_convert_u_i64 e, es
  | '\xb2', e :: es -> F64_promote_f32 e, es
  | '\xb3', e :: es -> F64_reinterpret_i64 e, es
  | '\xb4', e :: es -> I32_reinterpret_f32 e, es
  | '\xb5', e :: es -> I64_reinterpret_f64 e, es

  | '\xb6'..'\xff' as b, _ -> illegal s (pos s - 1) b

  | _ -> error s (len s) "unexpected end of function"

and decode_target s =
  let x = u16 s in
  if x & 0x8000 = 0 then
    Case x
  else
    Case_br (x & 0x7fff)


(* Decode memory section *)

let decode_power_of_2 s =
  let n = u8 s in
  require (n < 64) s (pos s - 1) "shift value out of range";
  Int64.(shift_left 1L (of_int n))

let decode_memory_section s =
  if decode_section_header s <> `MemorySection then None else
  let initial = decode_power_of_2 s in (*TODO: leb128 of page sizes*)
  let max = decode_power_of_2 s in
  let exported = bool8 s in (*TODO: spec has name*)
  Some (initial, max, exported)


(* Decode type section *)

let decode_type_section s =
  if decode_section_header s <> `TypesSection then [] else
  let types = decode_vec (at decode_func_type) s in
  types


(* Decode import section *)

let decode_import s =
  let itype  = at decode_var s in
  let module_name = decode_name s in
  let func_name = decode_name s in
  {itype; module_name; func_name}

let decode_import_section s =
  if decode_section_header s <> `ImportSection then [] else
  let imports = decode_vec (at decode_import) s in
  imports


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
  let s' = substream s size in
  let es = decode_expr_block s' in
  require (eos s') s (pos s') ("unexpected opcode " ^ string_of_byte (peek s));
  es

let decode_func s =
  let flags = u8 s in (*TODO: validate*)
  let ftype = at decode_var s in
  let has_name = bit 0 flags in
  let has_locals = bit 2 flags in
  let exported = bit 3 flags in
  let name = if has_name then Some (decode_name s) else None in (*TODO*)
  let locals = if has_locals then decode_locals s else [] in
  let body = at decode_body s in
  {ftype; locals; body}

let decode_func_section s =
  if decode_section_header s <> `FuncSection then [] else
  let funcs = decode_vec (at decode_func) s in
  funcs


(* Decode export section *)

let decode_import s =
  let func = at decode_var s in
  let name = at decode_name s in
  {func; name}

let decode_export_section s =
  if decode_section_header s <> `ExportSection then [] else
  let exports = decode_vec (at decode_import) s in
  exports


(* Decode data section *)

let decode_segment s =
  let addr = Int64.of_int32 (u32 s) logand 0xffffffffL in
  let offset = u32 s in
  let size = u32 s in
  let init = bool8 s in (*TODO: unused*)
  let data = bytes s offset size in
  {addr; data}

let decode_data_section s =
  if decode_section_header s <> `DataSection then [] else
  let segments = decode_vec (at decode_segment) s in
  segments


(* Decode table section *)

let decode_table_section s =
  if decode_section_header s <> `TableSection then [] else
  let table = decode_vec (at decode_var) s in
  table


(* Decode module *)

let decode_end s =
  if decode_section_header s <> `EndSection then
    error s (pos s - 1) "misplaced or duplicate section"

let decode_module s =
  let mem = decode_memory_section s in
  let types = decode_type_section s in
  let imports = decode_import_section s in
  let funcs = decode_func_section s in
  let exports = decode_export_section s in
  let table = decode_table_section s in
  let segments = decode_data_section s in (*TODO: merge with memory?*)
  decode_end s;
  let memory =
    match mem with
    | None when segments = [] -> None
    | None -> error s 0 "segment section without data section"
    | Some (initial, max, exported) -> Some {initial; max; segments} (*TODO: export name*)
  in {memory; types; funcs; imports; exports; table}

let decode name b = at decode_module (stream name b)
