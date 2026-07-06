open Ast

let parse source =
  let lexbuf = Lexing.from_string source in
  Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf

let assert_match msg ok =
  if not ok then failwith msg

let rec binop e op l r =
  match e with
  | Binary (e1, o, e2) -> o = op && exp_eq e1 l && exp_eq e2 r
  | _ -> false

and exp_eq e expected =
  match e, expected with
  | IntLit n, IntLit m -> n = m
  | Var a, Var b -> a = b
  | Unary (o1, e1), Unary (o2, e2) -> o1 = o2 && exp_eq e1 e2
  | Binary (a1, o1, b1), Binary (a2, o2, b2) ->
    o1 = o2 && exp_eq a1 a2 && exp_eq b1 b2
  | Call (f1, args1), Call (f2, args2) ->
    f1 = f2 && List.length args1 = List.length args2 && List.for_all2 exp_eq args1 args2
  | _ -> false

let return_exp ast =
  match ast with
  | [ FuncDef { body = [ Return (Some e) ] } ] -> e
  | _ -> failwith "expected single return in main"

let test name f =
  try
    f ();
    Printf.printf "[PASS] %s\n" name
  with e ->
    Printf.printf "[FAIL] %s: %s\n" name (Printexc.to_string e);
    raise e

let () =
  test "main only" (fun () ->
    let ast = parse "int main() { return 0; }" in
    assert_match "single main" (match ast with [ FuncDef fd ] -> fd.name = "main" | _ -> false));

  test "global const and var" (fun () ->
    let ast = parse "const int N = 42; int g = 0; int main() { return g; }" in
    assert_match "three top levels" (List.length ast = 3);
    assert_match "global const"
      (match List.hd ast with
       | GlobalConstDecl ("N", IntLit 42) -> true
       | _ -> false);
    assert_match "global var"
      (match List.nth ast 1 with
       | GlobalVarDecl ("g", IntLit 0) -> true
       | _ -> false));

  test "multi-param function" (fun () ->
    let ast = parse "int add(int a, int b) { return a + b; } int main() { return 0; }" in
    assert_match "add params"
      (match List.hd ast with
       | FuncDef { name = "add"; params = [ "a"; "b" ]; ret_type = IntRet } -> true
       | _ -> false));

  test "void function" (fun () ->
    let ast = parse "void f() { ; } int main() { return 0; }" in
    assert_match "void ret"
      (match List.hd ast with
       | FuncDef { name = "f"; ret_type = VoidRet; body = [ Empty ] } -> true
       | _ -> false));

  test "nested block" (fun () ->
    let ast = parse "int main() { { { int x = 1; } } return 0; }" in
    assert_match "nested blocks"
      (match ast with
       | [ FuncDef { body = [ Block [ Block [ VarDecl ("x", IntLit 1) ] ]; Return (Some (IntLit 0)) ]; _ } ]
         -> true
       | _ -> false));

  test "while break continue" (fun () ->
    let ast = parse "int main() { while (1) { break; continue; } return 0; }" in
    assert_match "while with break/continue"
      (match ast with
       | [ FuncDef { body = [ While (_, Block [ Break; Continue ]); Return (Some (IntLit 0)) ] } ]
         -> true
       | _ -> false));

  test "precedence: 1+2*3" (fun () ->
    let e = return_exp (parse "int main() { return 1 + 2 * 3; }") in
    assert_match "mul before add"
      (binop e Add (IntLit 1) (Binary (IntLit 2, Mul, IntLit 3))));

  test "precedence: a||b&&c" (fun () ->
    let e = return_exp (parse "int main() { return a || b && c; }") in
    assert_match "and before or"
      (binop e Or (Var "a") (Binary (Var "b", And, Var "c"))));

  test "precedence: !-x" (fun () ->
    let e = return_exp (parse "int main() { return !-x; }") in
    assert_match "not of minus x"
      (match e with
       | Unary (Not, Unary (UMinus, Var "x")) -> true
       | _ -> false));

  test "function call foo(1, 2)" (fun () ->
    let ast = parse "int foo(int a, int b) { return a; } int main() { return foo(1, 2); }" in
    let e =
      match List.nth ast 1 with
      | FuncDef { body = [ Return (Some e) ] } -> e
      | _ -> failwith "expected main with return"
    in
    assert_match "call with two args" (exp_eq e (Call ("foo", [ IntLit 1; IntLit 2 ]))));

  test "if-else" (fun () ->
    let ast = parse "int main() { if (1) return 0; else return 1; }" in
    assert_match "if else"
      (match ast with
       | [ FuncDef { body = [ If (IntLit 1, Return (Some (IntLit 0)), Some (Return (Some (IntLit 1)))) ] } ]
         -> true
       | _ -> false));

  test "subtraction 1-2" (fun () ->
    let e = return_exp (parse "int main() { return 1-2; }") in
    assert_match "1 sub 2" (binop e Sub (IntLit 1) (IntLit 2)));

  test "negative literal -5" (fun () ->
    let e = return_exp (parse "int main() { return -5; }") in
    assert_match "unary minus 5"
      (match e with
       | Unary (UMinus, IntLit 5) -> true
       | _ -> false));

  test "negative literal -0" (fun () ->
    let e = return_exp (parse "int main() { return -0; }") in
    assert_match "unary minus 0"
      (match e with
       | Unary (UMinus, IntLit 0) -> true
       | _ -> false));

  test "negative variable -x" (fun () ->
    let e = return_exp (parse "int main() { return -x; }") in
    assert_match "unary minus x"
      (match e with
       | Unary (UMinus, Var "x") -> true
       | _ -> false));

  test "negative paren -(1+2)" (fun () ->
    let e = return_exp (parse "int main() { return -(1+2); }") in
    assert_match "unary minus of sum"
      (match e with
       | Unary (UMinus, Binary (IntLit 1, Add, IntLit 2)) -> true
       | _ -> false));

  test "global const negative" (fun () ->
    let ast = parse "const int N = -10; int main() { return 0; }" in
    assert_match "const init negative"
      (match ast with
       | [ GlobalConstDecl ("N", Unary (UMinus, IntLit 10)); FuncDef _ ] -> true
       | _ -> false));

  test "double unary --5" (fun () ->
    let e = return_exp (parse "int main() { return --5; }") in
    assert_match "double minus"
      (match e with
       | Unary (UMinus, Unary (UMinus, IntLit 5)) -> true
       | _ -> false));

  Printf.printf "\nAll parser tests passed.\n"
