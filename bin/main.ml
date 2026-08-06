(** ToyC compiler entry point: stdin -> stdout *)

(* Off unless asked for: performance testing passes -opt, so gating the
   IR passes behind it keeps functional testing on the path with fewer
   transformations. Codegen-level work (register targeting, fused
   compare-and-branch, immediate folding) applies either way. *)
let optimize = ref false

let options =
  [ "-opt", Arg.Set optimize, " Enable optimization passes";
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
