exception Syntax of Source.region * string

type 'a start =
  | Module : Ast.module_ start
  | Script : Script.script start
  | Script1 : Script.script start

val parse : string -> Lexing.lexbuf -> 'a start -> 'a (* raise Syntax *)

val string_to_script : string -> Script.script (* raise Syntax *)
val string_to_module : string -> Ast.module_ (* raise Syntax *)

(*
val string_of_module : Ast.module_
*)