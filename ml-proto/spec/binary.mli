exception Decoding of Source.region * string

val decode : string -> bytes -> Ast.module_ (* raise Decoding *)

(*
val encode : Ast.module_ -> bytes
*)