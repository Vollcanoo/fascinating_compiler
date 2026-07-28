let parse source =
  let lexbuf = Lexing.from_string source in
  Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf

let check source = Analysis.Semantic.check (parse source)

let expect_error source =
  let failed =
    try
      check source;
      false
    with Failure _ -> true
  in
  if not failed then failwith "expected semantic error"

let find_global name (program : Backend.Ir.program) =
  List.find_opt
    (function
      | Backend.Ir.GConst (n, _) | Backend.Ir.GVar (n, _) -> n = name)
    program.globals

let () =
  (* A void call is legal as an expression statement, but not as a value. *)
  check "void f() { } int main() { f(); return 0; }";
  expect_error "void f() { } int main() { return f(); }";
  expect_error "void f() { } int main() { int x = f(); return x; }";

  (* Constant conditions participate in reachable-path return analysis. *)
  check "int main() { if (1) return 1; }";

  (* A local value shadows a function in the ordinary identifier namespace. *)
  expect_error
    "int f() { return 1; } int main() { int f = 0; return f(); }";

  (* Compile-time logical operators must retain C short-circuit behavior. *)
  let ast = parse "const int x = 0 && (1 / 0); int main() { return x; }" in
  Analysis.Semantic.check ast;
  let program = Backend.Ir.lower ast in
  (match find_global "x" program with
   | Some (Backend.Ir.GConst (_, 0)) -> ()
   | _ -> failwith "short-circuit constant was folded incorrectly");

  (* Every constant-expression operator accepted by semantics is lowered. *)
  let ast = parse "const int x = (1 < 2) && (3 != 4); int main() { return x; }" in
  Analysis.Semantic.check ast;
  let program = Backend.Ir.lower ast in
  (match find_global "x" program with
   | Some (Backend.Ir.GConst (_, 1)) -> ()
   | _ -> failwith "relational/logical global constant was folded incorrectly");

  (* Global data and functions share the assembler symbol namespace. *)
  expect_error "int f = 1; int f() { return 0; } int main() { return 0; }";
  expect_error "int f() { return 0; } int f = 1; int main() { return 0; }";

  (* A later global initializer may use the initial value of an earlier one. *)
  let ast = parse "int a = 2; int b = a + 3; int main() { return b; }" in
  Analysis.Semantic.check ast;
  let program = Backend.Ir.lower ast in
  match find_global "b" program with
  | Some (Backend.Ir.GVar (_, 5)) -> ()
  | _ -> failwith "global variable initializer was folded incorrectly"
