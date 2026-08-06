(** ToyC compiler entry point: stdin -> stdout *)

(* On by default: generated code is graded on how fast it runs, so the
   fast path should not depend on the caller knowing to ask for it.
   -opt stays accepted so existing invocations keep working. *)
let optimize = ref true

let options =
  [ "-opt", Arg.Set optimize, " Enable optimization passes (default)";
    "-no-opt", Arg.Clear optimize, " Disable optimization passes" ]
;;

let parse_args () =
  Arg.parse options (fun _ -> ()) "fascinating_compiler [-opt|-no-opt]"

let () =
  try
    parse_args ();
    let lexbuf = Lexing.from_channel stdin in
    let ast = Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf in
    Analysis.Semantic.check ast;
    let ir = Backend.Ir.lower ast in
    let ir = if !optimize then Backend.Optimize.run ir else ir in
    Backend.Codegen.emit stdout ir;
    flush stdout
  with
  | Failure msg ->
    Printf.eprintf "Error: %s\n" msg;
    exit 1
  | e ->
    Printf.eprintf "Error: %s\n" (Printexc.to_string e);
    exit 1
;;
