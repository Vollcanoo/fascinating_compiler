(** End-to-end regression driver.

    For every .tc file it compiles the program in-process, runs the generated
    assembly on the RV32IM simulator, and compares the exit code against the
    reference interpreter. Both compilation modes are checked, because the
    grader runs functional tests without -opt and performance tests with it.

    It also reports instructions retired, which is the metric used to track
    whether an optimization actually made generated code faster. *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let compile ~opt (source : string) : string =
  let lexbuf = Lexing.from_string source in
  let ast = Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf in
  Analysis.Semantic.check ast;
  let ir = Backend.Ir.lower ast in
  let ir = if opt then Backend.Optimize.run ir else ir in
  let tmp = Filename.temp_file "toyc" ".s" in
  let oc = open_out_bin tmp in
  Backend.Codegen.emit oc ir;
  close_out oc;
  let asm = read_file tmp in
  Sys.remove tmp;
  asm

let parse_ast (source : string) =
  let lexbuf = Lexing.from_string source in
  let ast = Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf in
  Analysis.Semantic.check ast;
  ast

(* Optional "// EXPECT: n" header, cross-checking the reference interpreter. *)
let declared_expectation (source : string) : int option =
  let lines = String.split_on_char '\n' source in
  let rec scan = function
    | [] -> None
    | line :: rest ->
      let line = String.trim line in
      let marker = "// EXPECT:" in
      let n = String.length marker in
      if String.length line > n && String.sub line 0 n = marker then
        int_of_string_opt
          (String.trim (String.sub line n (String.length line - n)))
      else if line = "" || (String.length line >= 2 && String.sub line 0 2 = "//")
      then scan rest
      else None
  in
  scan lines

type outcome =
  | Pass of int (* instructions retired *)
  | Fail of string

let check_one ~opt ~source ~reference =
  match compile ~opt source with
  | exception e -> Fail (Printf.sprintf "compile: %s" (Printexc.to_string e))
  | asm ->
    (match Rv32.simulate asm with
     | exception Rv32.Sim_error msg -> Fail (Printf.sprintf "simulate: %s" msg)
     | exception e -> Fail (Printf.sprintf "simulate: %s" (Printexc.to_string e))
     | result ->
       let want = reference land 0xFF in
       if result.Rv32.exit_code = want then Pass result.Rv32.retired
       else
         Fail
           (Printf.sprintf "exit code %d, expected %d" result.Rv32.exit_code want))

let collect_cases dirs =
  List.concat_map
    (fun dir ->
      if not (Sys.file_exists dir) then []
      else
        Sys.readdir dir |> Array.to_list
        |> List.filter (fun f -> Filename.check_suffix f ".tc")
        |> List.sort compare
        |> List.map (fun f -> Filename.concat dir f))
    dirs

let () =
  let dirs = ref [] in
  let dump = ref None in
  let speclist =
    [ ("-dump", Arg.String (fun s -> dump := Some s),
       "<case> print generated assembly for a case and exit") ]
  in
  Arg.parse speclist (fun d -> dirs := d :: !dirs) "regress [dirs]";
  let dirs =
    match List.rev !dirs with
    | [] -> [ "test/cases"; "test/bench" ]
    | ds -> ds
  in
  let cases = collect_cases dirs in
  if cases = [] then begin
    prerr_endline "regress: no .tc cases found";
    exit 1
  end;
  (match !dump with
   | Some name ->
     let path =
       List.find_opt (fun p -> Filename.basename p = name
                               || Filename.remove_extension (Filename.basename p) = name)
         cases
     in
     (match path with
      | None -> Printf.eprintf "no such case: %s\n" name; exit 1
      | Some path ->
        let source = read_file path in
        print_string (compile ~opt:true source);
        exit 0)
   | None -> ());

  let failures = ref 0 in
  let total_plain = ref 0 in
  let total_opt = ref 0 in
  Printf.printf "%-28s %10s %10s  %s\n" "case" "base" "-opt" "status";
  Printf.printf "%s\n" (String.make 66 '-');
  List.iter
    (fun path ->
      let name = Filename.remove_extension (Filename.basename path) in
      let source = read_file path in
      match parse_ast source with
      | exception e ->
        incr failures;
        Printf.printf "%-28s %10s %10s  FRONTEND: %s\n" name "-" "-"
          (Printexc.to_string e)
      | ast ->
        (match Interp.run ast with
         | exception e ->
           incr failures;
           Printf.printf "%-28s %10s %10s  REFERENCE: %s\n" name "-" "-"
             (Printexc.to_string e)
         | reference ->
           let declared_ok =
             match declared_expectation source with
             | None -> None
             | Some d ->
               if d land 0xFF = reference land 0xFF then None
               else
                 Some
                   (Printf.sprintf "declared EXPECT %d disagrees with reference %d"
                      d reference)
           in
           let plain = check_one ~opt:false ~source ~reference in
           let opted = check_one ~opt:true ~source ~reference in
           let cell = function Pass n -> string_of_int n | Fail _ -> "-" in
           let status =
             match (declared_ok, plain, opted) with
             | Some msg, _, _ -> "FAIL  " ^ msg
             | None, Fail m, _ -> "FAIL  base: " ^ m
             | None, _, Fail m -> "FAIL  -opt: " ^ m
             | None, Pass a, Pass b ->
               total_plain := !total_plain + a;
               total_opt := !total_opt + b;
               "ok"
           in
           if status <> "ok" then incr failures;
           Printf.printf "%-28s %10s %10s  %s\n" name (cell plain) (cell opted)
             status))
    cases;
  Printf.printf "%s\n" (String.make 66 '-');
  Printf.printf "%-28s %10d %10d\n" "TOTAL retired" !total_plain !total_opt;
  Printf.printf "%d case(s), %d failure(s)\n" (List.length cases) !failures;
  if !failures > 0 then exit 1
