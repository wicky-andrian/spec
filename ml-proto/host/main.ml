let name = "wasm"
let version = "0.2"

let banner () =
  print_endline (name ^ " " ^ version ^ " spec interpreter")

let error at category msg =
  Script.trace ("Error (" ^ category ^ "): ");
  prerr_endline (Source.string_of_region at ^ ": " ^ msg);
  false

let process get_script =
  try
    let script = get_script () in
    Script.trace "Desugaring...";
    let script' = Script.desugar script in
    Script.trace "Running...";
    Script.run script';
    true
  with
  | Binary.Decoding (at, msg) -> error at "decoding error" msg
  | Sexpr.Syntax (at, msg) -> error at "syntax error" msg
  | Script.AssertFailure (at, msg) -> error at "assertion failure" msg
  | Check.Invalid (at, msg) -> error at "invalid module" msg
  | Eval.Trap (at, msg) -> error at "runtime trap" msg
  | Eval.Crash (at, msg) -> error at "runtime crash" msg
  | Builtins.Unknown (at, msg) -> error at "unknown built-in" msg

let process_textual name lexbuf start =
  process (fun _ -> Sexpr.parse name lexbuf start)

let process_binary name buf =
  let open Source in
  process (fun _ -> let m = Binary.decode name buf in [Script.Define m @@ m.at])

let process_string name string =
  Script.trace ("Executing (\"" ^ String.escaped string ^ "\")...");
  let lexbuf = Lexing.from_string string in
  Script.trace "Parsing...";
  let success = process_textual name lexbuf Sexpr.Script in
  if not success then exit 1

let process_file file =
  Script.trace ("Loading (" ^ file ^ ")...");
  let ic = open_in file in
  try
    let lexbuf = Lexing.from_channel ic in
    Script.trace "Parsing...";
    let success = process_textual file lexbuf Sexpr.Script in
    close_in ic;
    if not success then exit 1
  with exn -> close_in ic; raise exn

let process_bin file =
  Script.trace ("Loading (" ^ file ^ ")...");
  let ic = open_in_bin file in
  try
    let len = in_channel_length ic in
    let buf = Bytes.make len '\x00' in
    really_input ic buf 0 len;
    Script.trace "Decoding...";
    let success = process_binary file buf in
    close_in ic;
    if not success then exit 1
  with exn -> close_in ic; raise exn

let process_arg = function
  | `Eval prog -> process_string "arg" prog
  | `File file when Filename.check_suffix file "wast" -> process_file file
  | `File file when Filename.check_suffix file "wasm" -> process_bin file
  | `File file ->
    prerr_endline (file ^ ": unrecognized file type");
    exit 1

let continuing = ref false

let lexbuf_stdin buf len =
  let prompt = if !continuing then "  " else "> " in
  print_string prompt; flush_all ();
  continuing := true;
  let rec loop i =
    if i = len then i else
    let ch = input_char stdin in
    Bytes.set buf i ch;
    if ch = '\n' then i + 1 else loop (i + 1)
  in
  let n = loop 0 in
  if n = 1 then continuing := false else Script.trace "Parsing...";
  n

let rec process_stdin () =
  banner ();
  let lexbuf = Lexing.from_function lexbuf_stdin in
  let rec loop () =
    let success = process_textual "stdin" lexbuf Sexpr.Script1 in
    if not success then Lexing.flush_input lexbuf;
    if Lexing.(lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len - 1) then
      continuing := false;
    loop ()
  in
  try loop () with End_of_file ->
    print_endline "";
    Script.trace "Bye."

let usage = "Usage: " ^ name ^ " [option] [file ...]"
let args = ref []
let argspec = Arg.align
[
  "-", Arg.Set Flags.interactive,
    " run interactively (default if no files given)";
  "--eval", Arg.String (fun prog -> args := !args @ [`Eval prog]),
    " evaluate string";
  "--invoke", Arg.String (fun name ->
    args := !args @ [`Eval ("(invoke \"" ^ name ^ "\")")]), " invoke export";
  "-s", Arg.Set Flags.print_sig, " show module signatures";
  "-d", Arg.Set Flags.dry, " dry, do not run program";
  "-t", Arg.Set Flags.trace, " trace execution";
  "-v", Arg.Unit banner, " show version"
]

let () =
  Printexc.record_backtrace true;
  try
    Arg.parse argspec (fun file -> args := !args @ [`File file]) usage;
    if !args = [] then Flags.interactive := true;
    List.iter process_arg !args;
    if !Flags.interactive then process_stdin ()
  with exn ->
    flush_all ();
    prerr_endline
      (Sys.argv.(0) ^ ": uncaught exception " ^ Printexc.to_string exn);
    Printexc.print_backtrace stderr;
    exit 2
