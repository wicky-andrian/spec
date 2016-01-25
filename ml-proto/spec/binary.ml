exception Decoding of int * string


let error pos msg = raise (Decoding (i, msg))
let require b pos msg = if not b then error pos msg


(* Decoding stream *)

type stream = {bytes : bytes; mutable pos : int}

let stream b = {bytes = b; pos = 0}
let len s = Bytes.length s.bytes
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


(* Decode immediates *)

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
  let x = Int64.of_int (b & 0x7f) in
  if b & 0x80 = 0 then x else Int64.(logor x (shift_left (leb128 s) 7))
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

let rec decode_expr s =
  let open Ast in
  match get s with
  | '\x00' -> Nop
  | '\x01' ->
    let len = u8 s in
    let es = repeat len decode_expr s in
    Block es
  | '\x02' ->
    let len = u8 s in
    let es = repeat len decode_expr s in
    Loop es
  | '\x03' ->
    let e1 = decode_expr s in
    let e2 = decode_expr s in
    If (e1, e2)
  | '\x04' ->
    let e1 = decode_expr s in
    let e2 = decode_expr s in
    let e3 = decode_expr s in
    If_else (e1, e2, e3)
  | '\x05' ->
    let e1 = decode_expr s in
    let e2 = decode_expr s in
    let e3 = decode_expr s in
    Select (e1, e2, e3)
  | '\x06' ->
    let x = u8 s in
    let eo = decode_expr_opt s in
    Br (x, eo)
  | '\x07' ->
    let x = u8 s in
    let eo = decode_expr_opt s in
    let e = decode_expr s in
    Br_if (x, eo, e)
  | '\x08' ->
    let len_cases = u16 s in
    let len_targets = u16 s in  (*TODO: minus 1?*)
    require (len_targets = 0) (pos s - 2) "empty switch table";
    let ts = repeat (len_targets - 1) decode_target s in
    let t = decode_target s in
    let e = decode_expr s in
    let es = repeat len_cases decode_expr s in
    Tableswitch (e, ts, t, List.map (fun e -> [e]) es) (*TODO: fix AST*)

  | '\x09' -> I32_const (Int32.of_int (u8 s) & 0xffl) (*TODO: needed?*)
  | '\x0a' -> I32_const (u32 s)
  | '\x0b' -> I64_const (u64 s)
  | '\x0c' -> F32_const (f32 s)
  | '\x0d' -> F64_const (f64 s)

  | '\x0e' -> let x = leb128 s in Get_local (x)
  | '\x0f' -> let x = leb128 s in Set_local (x, decode_expr s)
  | '\x10' -> error (pos s - 1) "illegal load_global opcode"
  | '\x11' -> error (pos s - 1) "illegal store_global opcode"

  | '\x12' ->
    let x = leb128 s in
    let arity = (*TODO: from func table*) in
    let es = repeat arity decode_expr s in
    Call (x, es)
  | '\x13' ->
    let x = leb128 s in
    let arity = (*TODO: from type table*) in
    let e = decode_expr s in
    let es = repeat arity decode_expr s in
    Call_indirect (x, e, es)
  (*TODO: Call_import?*)

  | '\x14' ->
    let arity = (*TODO: from func table*) in
    let eo = if arity = 0 then None else Some (decode_expr s) in
    Return eo
  | '\x15' ->
    Unreachable

  (* '\x16'-'\x1f' are unused *)

  | '\x20' -> I32_load8_s (0, None, decode_expr s)
  | '\x21' -> I32_load8_u (0, None, decode_expr s)
  | '\x22' -> I32_load16_s (0, None, decode_expr s)
  | '\x23' -> I32_load16_u (0, None, decode_expr s)
  | '\x24' -> I64_load8_s (0, None, decode_expr s)
  | '\x25' -> I64_load8_u (0, None, decode_expr s)
  | '\x26' -> I64_load16_s (0, None, decode_expr s)
  | '\x27' -> I64_load16_u (0, None, decode_expr s)
  | '\x28' -> I64_load32_s (0, None, decode_expr s)
  | '\x29' -> I64_load32_u (0, None, decode_expr s)
  | '\x2a' -> I32_load (0, None, decode_expr s)
  | '\x2b' -> I64_load (0, None, decode_expr s)
  | '\x2c' -> F32_load (0, None, decode_expr s)
  | '\x2d' -> F64_load (0, None, decode_expr s)

  | '\x2e' -> let e1, e2 = decode_expr2 s in I32_store8 (0, None, e1, e2)
  | '\x2f' -> let e1, e2 = decode_expr2 s in I32_store16 (0, None, e1, e2)
  | '\x30' -> let e1, e2 = decode_expr2 s in I64_store8 (0, None, e1, e2)
  | '\x31' -> let e1, e2 = decode_expr2 s in I64_store16 (0, None, e1, e2)
  | '\x32' -> let e1, e2 = decode_expr2 s in I64_store32 (0, None, e1, e2)
  | '\x33' -> let e1, e2 = decode_expr2 s in I32_store (0, None, e1, e2)
  | '\x34' -> let e1, e2 = decode_expr2 s in I64_store (0, None, e1, e2)
  | '\x35' -> let e1, e2 = decode_expr2 s in F32_store (0, None, e1, e2)
  | '\x36' -> let e1, e2 = decode_expr2 s in F64_store (0, None, e1, e2)

  (* '\x37' is unused *)
  (* '\x38' is unused *)
  | '\x39' -> Grow_memory (decode_expr s)
  (* '\x3a' is unused *)
  | '\x3b' -> Memory_size

  | '\x40' -> let e1, e2 = decode_expr2 s in I32_add (e1, e2)
  | '\x41' -> let e1, e2 = decode_expr2 s in I32_sub (e1, e2)
  | '\x42' -> let e1, e2 = decode_expr2 s in I32_mul (e1, e2)
  | '\x43' -> let e1, e2 = decode_expr2 s in I32_div_s (e1, e2)
  | '\x44' -> let e1, e2 = decode_expr2 s in I32_div_u (e1, e2)
  | '\x45' -> let e1, e2 = decode_expr2 s in I32_rem_s (e1, e2)
  | '\x46' -> let e1, e2 = decode_expr2 s in I32_rem_u (e1, e2)
  | '\x47' -> let e1, e2 = decode_expr2 s in I32_and (e1, e2)
  | '\x48' -> let e1, e2 = decode_expr2 s in I32_or (e1, e2)
  | '\x49' -> let e1, e2 = decode_expr2 s in I32_xor (e1, e2)
  | '\x4a' -> let e1, e2 = decode_expr2 s in I32_shl (e1, e2)
  | '\x4b' -> let e1, e2 = decode_expr2 s in I32_shr_u (e1, e2)
  | '\x4c' -> let e1, e2 = decode_expr2 s in I32_shr_s (e1, e2)
  | '\x4d' -> let e1, e2 = decode_expr2 s in I32_eq (e1, e2)
  | '\x4e' -> let e1, e2 = decode_expr2 s in I32_ne (e1, e2)
  | '\x4f' -> let e1, e2 = decode_expr2 s in I32_lt_s (e1, e2)
  | '\x50' -> let e1, e2 = decode_expr2 s in I32_le_s (e1, e2)
  | '\x51' -> let e1, e2 = decode_expr2 s in I32_lt_u (e1, e2)
  | '\x52' -> let e1, e2 = decode_expr2 s in I32_le_u (e1, e2)
  | '\x53' -> let e1, e2 = decode_expr2 s in I32_gt_s (e1, e2)
  | '\x54' -> let e1, e2 = decode_expr2 s in I32_ge_s (e1, e2)
  | '\x55' -> let e1, e2 = decode_expr2 s in I32_gt_u (e1, e2)
  | '\x56' -> let e1, e2 = decode_expr2 s in I32_ge_u (e1, e2)
  | '\x57' -> let e1, e2 = decode_expr2 s in I32_clz (e1, e2)
  | '\x58' -> let e1, e2 = decode_expr2 s in I32_ctz (e1, e2)
  | '\x59' -> let e1, e2 = decode_expr2 s in I32_popcnt (e1, e2)
  | '\x5a' -> let e1, e2 = decode_expr2 s in I32_not (e1, e2) (*TODO*)

  | '\x5b' -> let e1, e2 = decode_expr2 s in I64_add (e1, e2)
  | '\x5c' -> let e1, e2 = decode_expr2 s in I64_sub (e1, e2)
  | '\x5d' -> let e1, e2 = decode_expr2 s in I64_mul (e1, e2)
  | '\x5e' -> let e1, e2 = decode_expr2 s in I64_div_s (e1, e2)
  | '\x5f' -> let e1, e2 = decode_expr2 s in I64_div_u (e1, e2)
  | '\x60' -> let e1, e2 = decode_expr2 s in I64_rem_s (e1, e2)
  | '\x61' -> let e1, e2 = decode_expr2 s in I64_rem_u (e1, e2)
  | '\x62' -> let e1, e2 = decode_expr2 s in I64_and (e1, e2)
  | '\x63' -> let e1, e2 = decode_expr2 s in I64_or (e1, e2)
  | '\x64' -> let e1, e2 = decode_expr2 s in I64_xor (e1, e2)
  | '\x65' -> let e1, e2 = decode_expr2 s in I64_shl (e1, e2)
  | '\x66' -> let e1, e2 = decode_expr2 s in I64_shr_u (e1, e2)
  | '\x67' -> let e1, e2 = decode_expr2 s in I64_shr_s (e1, e2)
  | '\x68' -> let e1, e2 = decode_expr2 s in I64_eq (e1, e2)
  | '\x69' -> let e1, e2 = decode_expr2 s in I64_ne (e1, e2)
  | '\x6a' -> let e1, e2 = decode_expr2 s in I64_lt_s (e1, e2)
  | '\x6b' -> let e1, e2 = decode_expr2 s in I64_le_s (e1, e2)
  | '\x6c' -> let e1, e2 = decode_expr2 s in I64_lt_u (e1, e2)
  | '\x6d' -> let e1, e2 = decode_expr2 s in I64_le_u (e1, e2)
  | '\x6e' -> let e1, e2 = decode_expr2 s in I64_gt_s (e1, e2)
  | '\x6f' -> let e1, e2 = decode_expr2 s in I64_ge_s (e1, e2)
  | '\x70' -> let e1, e2 = decode_expr2 s in I64_gt_u (e1, e2)
  | '\x71' -> let e1, e2 = decode_expr2 s in I64_ge_u (e1, e2)
  | '\x72' -> let e1, e2 = decode_expr2 s in I64_clz (e1, e2)
  | '\x73' -> let e1, e2 = decode_expr2 s in I64_ctyz (e1, e2)
  | '\x74' -> let e1, e2 = decode_expr2 s in I64_popcnt (e1, e2)

  | '\x75' -> let e1, e2 = decode_expr2 s in F32_add (e1, e2)
  | '\x76' -> let e1, e2 = decode_expr2 s in F32_sub (e1, e2)
  | '\x77' -> let e1, e2 = decode_expr2 s in F32_mul (e1, e2)
  | '\x78' -> let e1, e2 = decode_expr2 s in F32_div (e1, e2)
  | '\x79' -> let e1, e2 = decode_expr2 s in F32_min (e1, e2)
  | '\x7a' -> let e1, e2 = decode_expr2 s in F32_max (e1, e2)
  | '\x7b' -> let e1, e2 = decode_expr2 s in F32_abs (e1, e2)
  | '\x7c' -> let e1, e2 = decode_expr2 s in F32_neg (e1, e2)
  | '\x7d' -> let e1, e2 = decode_expr2 s in F32_copysign (e1, e2)
  | '\x7e' -> let e1, e2 = decode_expr2 s in F32_ceil (e1, e2)
  | '\x7f' -> let e1, e2 = decode_expr2 s in F32_floor (e1, e2)
  | '\x80' -> let e1, e2 = decode_expr2 s in F32_trunc (e1, e2)
  | '\x81' -> let e1, e2 = decode_expr2 s in F32_nearest (e1, e2)
  | '\x82' -> let e1, e2 = decode_expr2 s in F32_sqrt (e1, e2)
  | '\x83' -> let e1, e2 = decode_expr2 s in F32_eq (e1, e2)
  | '\x84' -> let e1, e2 = decode_expr2 s in F32_ne (e1, e2)
  | '\x85' -> let e1, e2 = decode_expr2 s in F32_lt (e1, e2)
  | '\x86' -> let e1, e2 = decode_expr2 s in F32_le (e1, e2)
  | '\x87' -> let e1, e2 = decode_expr2 s in F32_gt (e1, e2)
  | '\x88' -> let e1, e2 = decode_expr2 s in F32_ge (e1, e2)

  | '\x89' -> let e1, e2 = decode_expr2 s in F64_add (e1, e2)
  | '\x8a' -> let e1, e2 = decode_expr2 s in F64_sub (e1, e2)
  | '\x8b' -> let e1, e2 = decode_expr2 s in F64_mul (e1, e2)
  | '\x8c' -> let e1, e2 = decode_expr2 s in F64_div (e1, e2)
  | '\x8d' -> let e1, e2 = decode_expr2 s in F64_min (e1, e2)
  | '\x8e' -> let e1, e2 = decode_expr2 s in F64_max (e1, e2)
  | '\x8f' -> let e1, e2 = decode_expr2 s in F64_abs (e1, e2)
  | '\x90' -> let e1, e2 = decode_expr2 s in F64_neg (e1, e2)
  | '\x91' -> let e1, e2 = decode_expr2 s in F64_copysign (e1, e2)
  | '\x92' -> let e1, e2 = decode_expr2 s in F64_ceil (e1, e2)
  | '\x93' -> let e1, e2 = decode_expr2 s in F64_floor (e1, e2)
  | '\x94' -> let e1, e2 = decode_expr2 s in F64_trunc (e1, e2)
  | '\x95' -> let e1, e2 = decode_expr2 s in F64_nearest (e1, e2)
  | '\x96' -> let e1, e2 = decode_expr2 s in F64_sqrt (e1, e2)
  | '\x97' -> let e1, e2 = decode_expr2 s in F64_eq (e1, e2)
  | '\x98' -> let e1, e2 = decode_expr2 s in F64_ne (e1, e2)
  | '\x99' -> let e1, e2 = decode_expr2 s in F64_lt (e1, e2)
  | '\x9a' -> let e1, e2 = decode_expr2 s in F64_le (e1, e2)
  | '\x9b' -> let e1, e2 = decode_expr2 s in F64_gt (e1, e2)
  | '\x9c' -> let e1, e2 = decode_expr2 s in F64_ge (e1, e2)

  | '\x9d' -> let e1, e2 = decode_expr2 s in I32_trunc_s_f32 (e1, e2)
  | '\x9e' -> let e1, e2 = decode_expr2 s in I32_trunc_s_f64 (e1, e2)
  | '\x9f' -> let e1, e2 = decode_expr2 s in I32_trunc_u_f32 (e1, e2)
  | '\xa0' -> let e1, e2 = decode_expr2 s in I32_trunc_u_f64 (e1, e2)
  | '\xa1' -> let e1, e2 = decode_expr2 s in I32_wrap_i64 (e1, e2)
  | '\xa2' -> let e1, e2 = decode_expr2 s in I32_trunc_s_f32 (e1, e2)
  | '\xa3' -> let e1, e2 = decode_expr2 s in I32_trunc_s_f64 (e1, e2)
  | '\xa4' -> let e1, e2 = decode_expr2 s in I32_trunc_u_f32 (e1, e2)
  | '\xa5' -> let e1, e2 = decode_expr2 s in I32_trunc_u_f64 (e1, e2)
  | '\xa6' -> let e1, e2 = decode_expr2 s in I64_extend_s_i32 (e1, e2)
  | '\xa7' -> let e1, e2 = decode_expr2 s in I64_extend_u_i32 (e1, e2)
  | '\xa8' -> let e1, e2 = decode_expr2 s in F32_convert_s_i32 (e1, e2)
  | '\xa9' -> let e1, e2 = decode_expr2 s in F32_convert_u_i32 (e1, e2)
  | '\xaa' -> let e1, e2 = decode_expr2 s in F32_convert_s_i64 (e1, e2)
  | '\xab' -> let e1, e2 = decode_expr2 s in F32_convert_u_i64 (e1, e2)
  | '\xac' -> let e1, e2 = decode_expr2 s in F32_demote_f64 (e1, e2)
  | '\xad' -> let e1, e2 = decode_expr2 s in F32_reinterpret_i32 (e1, e2)
  | '\xae' -> let e1, e2 = decode_expr2 s in F64_convert_s_i32 (e1, e2)
  | '\xaf' -> let e1, e2 = decode_expr2 s in F64_convert_u_i32 (e1, e2)
  | '\xb0' -> let e1, e2 = decode_expr2 s in F64_convert_s_i64 (e1, e2)
  | '\xb1' -> let e1, e2 = decode_expr2 s in F64_convert_u_i64 (e1, e2)
  | '\xb2' -> let e1, e2 = decode_expr2 s in F64_promote_f32 (e1, e2)
  | '\xb3' -> let e1, e2 = decode_expr2 s in F64_reinterpret_i64 (e1, e2)
  | '\xb4' -> let e1, e2 = decode_expr2 s in I32_reinterpret_f32 (e1, e2)
  | '\xb5' -> let e1, e2 = decode_expr2 s in I64_reinterpret_f64 (e1, e2)

  | _ -> error (pos s - 1) "invalid operator opcode"

and decode_expr2 s =
  let e1 = decode_expr s in
  let e2 = decode_expr s in
  e1, e2

and decode_expr_opt s in
  match peek s with
  | '\x00' -> adv s; None
  | _ -> Some (decode_expr s)

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
  let exported = bool8 s in (*TODO: not specced*)
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
