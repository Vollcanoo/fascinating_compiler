open Ast
open Backend.Ir

let parse source =
  let lexbuf = Lexing.from_string source in
  Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf

let lower source =
  let ast = parse source in
  Analysis.Semantic.check ast;
  Backend.Ir.lower ast

let find_func name (p : program) =
  List.find (fun (f : func_ir) -> f.name = name) p.funcs

(* Minimal interpreter for a single call-free, global-free function, used to
   check that optimization never changes what a function computes. Params
   occupy temps 0..n-1, matching how Ir.gen_func assigns them. *)
let interpret (f : func_ir) (args : int list) : int option =
  let temps = Array.make (max f.temp_count 1) 0 in
  List.iteri (fun i v -> if i < Array.length temps then temps.(i) <- v) args;
  let body = Array.of_list f.body in
  let labels = Hashtbl.create 16 in
  Array.iteri
    (fun i instr ->
       match instr with
       | ILabel l -> Hashtbl.replace labels l i
       | _ -> ())
    body;
  let eval_binop op a b =
    match op with
    | Add -> a + b
    | Sub -> a - b
    | Mul -> a * b
    | Div -> a / b
    | Mod -> a mod b
    | Lt -> if a < b then 1 else 0
    | Gt -> if a > b then 1 else 0
    | Le -> if a <= b then 1 else 0
    | Ge -> if a >= b then 1 else 0
    | Eq -> if a = b then 1 else 0
    | Ne -> if a <> b then 1 else 0
    | And -> if a <> 0 && b <> 0 then 1 else 0
    | Or -> if a <> 0 || b <> 0 then 1 else 0
  in
  let eval_unary op a =
    match op with
    | UPlus -> a
    | UMinus -> -a
    | Not -> if a = 0 then 1 else 0
  in
  let rec run i =
    if i >= Array.length body then None
    else
      match body.(i) with
      | ILoad (d, Imm n) -> temps.(d) <- n; run (i + 1)
      | ILoad (d, Temp s) -> temps.(d) <- temps.(s); run (i + 1)
      | ILoad (_, Name _) | ILoadGlobal _ | IStoreGlobal _ ->
        failwith "test interpreter does not support globals"
      | IBinOp (d, op, a, b) ->
        temps.(d) <- eval_binop op temps.(a) temps.(b); run (i + 1)
      | IUnaryOp (d, op, s) -> temps.(d) <- eval_unary op temps.(s); run (i + 1)
      | ICall _ | ICallVoid _ ->
        failwith "test interpreter does not support calls"
      | ILabel _ -> run (i + 1)
      | IJump l -> run (Hashtbl.find labels l)
      | IBranchTrue (s, l) ->
        if temps.(s) <> 0 then run (Hashtbl.find labels l) else run (i + 1)
      | IBranchFalse (s, l) ->
        if temps.(s) = 0 then run (Hashtbl.find labels l) else run (i + 1)
      | IReturn (Some s) -> Some temps.(s)
      | IReturn None -> None
      | IComment _ -> run (i + 1)
  in
  run 0

let test name f =
  try
    f ();
    Printf.printf "[PASS] %s\n" name
  with e ->
    Printf.printf "[FAIL] %s: %s\n" name (Printexc.to_string e);
    raise e

let assert_eq msg expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected %d, got %d" msg expected actual)

let has_branch (f : func_ir) =
  List.exists
    (function IBranchTrue _ | IBranchFalse _ -> true | _ -> false)
    f.body

let has_add (f : func_ir) =
  List.exists (function IBinOp (_, Add, _, _) -> true | _ -> false) f.body

let count_add (f : func_ir) =
  List.length
    (List.filter (function IBinOp (_, Add, _, _) -> true | _ -> false) f.body)

let has_imm (f : func_ir) n =
  List.exists (function ILoad (_, Imm m) -> m = n | _ -> false) f.body

let instr_def_for_test = function
  | ILoad (d, _) | ILoadGlobal (d, _)
  | IBinOp (d, _, _, _) | IUnaryOp (d, _, _) | ICall (d, _, _) -> Some d
  | ICallVoid _ | IStoreGlobal _ | ILabel _ | IJump _
  | IBranchTrue _ | IBranchFalse _ | IReturn _ | IComment _ -> None

let () =
  test "run wires up the optimizer (regression: used to be a no-op)"
    (fun () ->
       let program = lower "int main() { int a = 1 + 2; return a; }" in
       let optimized = Backend.Optimize.run program in
       let before = find_func "main" program in
       let after = find_func "main" optimized in
       if List.length after.body >= List.length before.body then
         failwith "Optimize.run did not shrink an obviously foldable function");

  test "constant folding + DCE preserve semantics" (fun () ->
      let program = lower "int main() { int a = 3; int b = 4; int c = a * b + 1; return c; }" in
      let before = find_func "main" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 13 (Option.get (interpret before []));
      assert_eq "optimized result" 13 (Option.get (interpret after []));
      if List.length after.body >= List.length before.body then
        failwith "constant folding did not reduce instruction count");

  test "dead branch elimination on a constant if/else" (fun () ->
      let program =
        lower "int main() { int x = 0; if (1) { x = 5; } else { x = 10; } return x; }"
      in
      let before = find_func "main" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 5 (Option.get (interpret before []));
      assert_eq "optimized result" 5 (Option.get (interpret after []));
      if has_branch after then
        failwith "constant if/else condition should leave no runtime branch";
      if has_imm after 10 then
        failwith "the never-taken else branch should have been pruned");

  test "while(0) loop body is unreachable and gets pruned" (fun () ->
      let program =
        lower "int main() { int x = 1; while (0) { x = x + 1; } return x; }"
      in
      let before = find_func "main" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 1 (Option.get (interpret before []));
      assert_eq "optimized result" 1 (Option.get (interpret after []));
      if has_add after then
        failwith "unreachable loop body should have been pruned");

  test "unused local computation is eliminated" (fun () ->
      let program = lower "int main() { int unused = 1 + 2; return 42; }" in
      let before = find_func "main" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 42 (Option.get (interpret before []));
      assert_eq "optimized result" 42 (Option.get (interpret after []));
      if has_imm after 1 || has_imm after 2 then
        failwith "dead computation for 'unused' should have been removed";
      if List.length after.body <> 2 then
        failwith
          (Printf.sprintf "expected fully-reduced body of 2 instrs, got %d"
             (List.length after.body)));

  test "loop that actually runs still computes the right answer" (fun () ->
      (* Guards against over-aggressive branch folding: the condition here
         is not a compile-time constant, so the loop must still execute. *)
      let program =
        lower "int main() { int i = 0; int sum = 0; while (i < 5) { sum = sum + i; i = i + 1; } return sum; }"
      in
      let before = find_func "main" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 10 (Option.get (interpret before []));
      assert_eq "optimized result" 10 (Option.get (interpret after [])));

  test "instruction scheduling fills a load/use gap with independent work"
    (fun () ->
       (* x = a+b; y = x+c; z = c+d; return y+z.
          y's def is a direct, zero-gap consumer of x in program order,
          while z is independent of both x and y. A hazard-aware
          scheduler has room to move z's computation ahead of y's to
          separate x's definition from its use. Hand-built (rather than
          parsed) so the dependency shape is exact and doesn't depend on
          how ir.ml happens to number temporaries. *)
       let before : Backend.Ir.func_ir = {
         name = "sched";
         ret_type = Ast.IntRet;
         params = [ "a"; "b"; "c"; "d" ];
         locals = [];
         body = [
           Backend.Ir.IBinOp (4, Ast.Add, 0, 1); (* x = a + b *)
           Backend.Ir.IBinOp (5, Ast.Add, 4, 2); (* y = x + c *)
           Backend.Ir.IBinOp (6, Ast.Add, 2, 3); (* z = c + d *)
           Backend.Ir.IBinOp (7, Ast.Add, 5, 6); (* y + z *)
           Backend.Ir.IReturn (Some 7);
         ];
         temp_count = 8;
       } in
       let after = Backend.Optimize.optimize_func before in
       assert_eq "unoptimized result" 13 (Option.get (interpret before [ 1; 2; 3; 4 ]));
       assert_eq "optimized result" 13 (Option.get (interpret after [ 1; 2; 3; 4 ]));
       let def_index temp =
         let rec find i = function
           | [] -> failwith (Printf.sprintf "temp %d not defined in scheduled body" temp)
           | instr :: rest ->
             (match instr_def_for_test instr with
              | Some d when d = temp -> i
              | _ -> find (i + 1) rest)
         in
         find 0 after.Backend.Ir.body
       in
       if not (def_index 6 < def_index 5) then
         failwith "independent z = c+d should have been scheduled ahead of y = x+c");

  test "common subexpression elimination reuses a repeated computation"
    (fun () ->
       (* params, not literals: operands must not be compile-time
          constants, otherwise constant folding alone (already tested
          above) would collapse everything and this wouldn't exercise
          CSE at all. `return x + y` is a genuinely separate addition
          (it still must run), so the reduction is 3 adds -> 2, not
          3 -> 1. *)
       let program =
         lower "int f(int a, int b) { int x = a + b; int y = a + b; return x + y; } int main() { return 0; }"
       in
       let before = find_func "f" program in
       let after = Backend.Optimize.optimize_func before in
       assert_eq "unoptimized result" 14 (Option.get (interpret before [ 3; 4 ]));
       assert_eq "optimized result" 14 (Option.get (interpret after [ 3; 4 ]));
       if count_add after >= count_add before then
         failwith
           (Printf.sprintf "expected the repeated a+b to be shared: %d adds before, %d after"
              (count_add before) (count_add after)));

  test "CSE recognizes commutative reordering (a+b vs b+a)" (fun () ->
      let program =
        lower "int f(int a, int b) { int x = a + b; int y = b + a; return x + y; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 14 (Option.get (interpret before [ 3; 4 ]));
      assert_eq "optimized result" 14 (Option.get (interpret after [ 3; 4 ]));
      if count_add after >= count_add before then
        failwith
          (Printf.sprintf "expected a+b and b+a to be recognized as the same expression: %d adds before, %d after"
             (count_add before) (count_add after)));

  test "CSE does not reuse a computation once an operand changes" (fun () ->
      let program =
        lower "int f(int a, int b) { int x = a + b; a = a + 1; int y = a + b; return x + y; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized result" 15 (Option.get (interpret before [ 3; 4 ]));
      assert_eq "optimized result" 15 (Option.get (interpret after [ 3; 4 ]));
      if count_add after <> count_add before then
        failwith
          (Printf.sprintf
             "the second a+b uses a reassigned a and must be recomputed, not reused: %d adds before, %d after"
             (count_add before) (count_add after)));

  (* Loop rotation moves the test below the body, so the entry jump is the
     only thing keeping a loop whose condition starts false from running
     its body once. Getting that wrong is silent: the code still
     assembles and still terminates, it just computes the wrong answer. *)
  test "rotated loop with a false condition never enters the body" (fun () ->
      let program =
        lower "int f(int n) { int s = 0; while (n > 0) { s = s + 100; n = n - 1; } return s; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized, zero iterations" 0 (Option.get (interpret before [ 0 ]));
      assert_eq "optimized, zero iterations" 0 (Option.get (interpret after [ 0 ]));
      assert_eq "unoptimized, three iterations" 300 (Option.get (interpret before [ 3 ]));
      assert_eq "optimized, three iterations" 300 (Option.get (interpret after [ 3 ])));

  test "break still leaves a rotated loop" (fun () ->
      let program =
        lower "int f(int n) { int s = 0; while (1) { if (s >= n) break; s = s + 1; } return s; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized" 5 (Option.get (interpret before [ 5 ]));
      assert_eq "optimized" 5 (Option.get (interpret after [ 5 ])));

  test "continue still re-tests a rotated loop" (fun () ->
      (* sums only the odd values below n, so a continue that skipped the
         test (or the increment) would change the total *)
      let program =
        lower "int f(int n) { int i = 0; int s = 0; while (i < n) { i = i + 1; if (i % 2 == 0) continue; s = s + i; } return s; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized" 25 (Option.get (interpret before [ 10 ]));
      assert_eq "optimized" 25 (Option.get (interpret after [ 10 ])));

  test "nested loops rotate independently" (fun () ->
      let program =
        lower "int f(int n) { int s = 0; int i = 0; while (i < n) { int j = 0; while (j < n) { s = s + 1; j = j + 1; } i = i + 1; } return s; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized" 49 (Option.get (interpret before [ 7 ]));
      assert_eq "optimized" 49 (Option.get (interpret after [ 7 ]));
      assert_eq "unoptimized, outer never runs" 0 (Option.get (interpret before [ 0 ]));
      assert_eq "optimized, outer never runs" 0 (Option.get (interpret after [ 0 ])));

  (* Identities settle the result from one operand alone, so they apply
     where constant folding cannot: the other side stays unknown. *)
  test "algebraic identities remove operations with an unknown operand"
    (fun () ->
       let program =
         lower "int f(int a) { int x = a * 1; int y = x + 0; int z = y - 0; return z / 1; } int main() { return 0; }"
       in
       let before = find_func "f" program in
       let after = Backend.Optimize.optimize_func before in
       assert_eq "unoptimized" 7 (Option.get (interpret before [ 7 ]));
       assert_eq "optimized" 7 (Option.get (interpret after [ 7 ]));
       let arithmetic =
         List.length
           (List.filter
              (function IBinOp (_, (Mul | Add | Sub | Div), _, _) -> true | _ -> false)
              after.body)
       in
       if arithmetic <> 0 then
         failwith
           (Printf.sprintf "every operation was an identity, %d survived" arithmetic));

  test "multiplying by zero drops the unknown side" (fun () ->
      let program =
        lower "int f(int a) { return a * 0; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized" 0 (Option.get (interpret before [ 99 ]));
      assert_eq "optimized" 0 (Option.get (interpret after [ 99 ]));
      if List.exists (function IBinOp (_, Mul, _, _) -> true | _ -> false) after.body then
        failwith "a * 0 still multiplies");

  test "identities do not fire when the operand is not the neutral one"
    (fun () ->
       (* guards against a rule matching too eagerly, which would be
          silent: the code still runs, it just computes something else *)
       let program =
         lower "int f(int a) { return a * 2 + 1; } int main() { return 0; }"
       in
       let before = find_func "f" program in
       let after = Backend.Optimize.optimize_func before in
       assert_eq "unoptimized" 15 (Option.get (interpret before [ 7 ]));
       assert_eq "optimized" 15 (Option.get (interpret after [ 7 ])));

  test "comparing a value with itself needs no comparison" (fun () ->
      let program =
        lower "int f(int a) { int b = a; if (a == b) return 1; return 0; } int main() { return 0; }"
      in
      let before = find_func "f" program in
      let after = Backend.Optimize.optimize_func before in
      assert_eq "unoptimized" 1 (Option.get (interpret before [ 5 ]));
      assert_eq "optimized" 1 (Option.get (interpret after [ 5 ])));

  Printf.printf "\nAll optimizer tests passed.\n"
