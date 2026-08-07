(** Backend invariants that are cheap to state on the generated assembly.

    Whether the generated code computes the right answer is checked end to end
    by test/regress, which runs every program in test/cases on the RV32
    simulator and compares against the reference interpreter. *)

open Backend

let compile ?(opt = false) source =
  let lexbuf = Lexing.from_string source in
  let ast = Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf in
  Analysis.Semantic.check ast;
  let program = Ir.lower ast in
  let program = if opt then Optimize.run program else program in
  Codegen.assembly program

let contains haystack needle =
  let n = String.length needle in
  let limit = String.length haystack - n in
  let rec loop i = i <= limit && (String.sub haystack i n = needle || loop (i + 1)) in
  n = 0 || loop 0

let fail_if condition message = if condition then failwith message

let distinct_homes message allocation a b =
  match Regalloc.location allocation a, Regalloc.location allocation b with
  | Regalloc.Reg x, Regalloc.Reg y when x = y -> failwith message
  | Regalloc.Spill x, Regalloc.Spill y when x = y -> failwith message
  | _ -> ()

let () =
  (* A value used at a loop header stays live across the whole back edge.  A
     textual live-interval allocator would happily give temporaries 0 and 1 the
     same register, and the loop body would then clobber the next condition. *)
  let loop_ir : Ir.func_ir = {
    name = "loop_liveness";
    ret_type = Ast.IntRet;
    params = [];
    body = [
      Ir.ILoad (0, Ir.Imm 5);
      Ir.ILabel ".Lloop";
      Ir.IBranchZero (Ir.Temp 0, ".Lloop_end");
      Ir.ILoad (1, Ir.Imm 1);
      Ir.IStoreGlobal ("sink", Ir.Temp 1);
      Ir.IJump ".Lloop";
      Ir.ILabel ".Lloop_end";
      Ir.ILoad (2, Ir.Imm 0);
      Ir.IReturn (Some (Ir.Temp 2));
    ];
    temp_count = 3;
  } in
  distinct_homes "loop-invariant value shares a home across the back edge"
    (Regalloc.allocate loop_ir) 0 1;

  (* Every incoming argument is copied to its home at entry, including ones the
     body never reads, so those copies must not overwrite one another. *)
  let params_ir : Ir.func_ir = {
    name = "parameter_homes";
    ret_type = Ast.IntRet;
    params = ["live"; "unused"];
    body = [
      Ir.ILoadParam (0, 0);
      Ir.ILoadParam (1, 1);
      Ir.IReturn (Some (Ir.Temp 0));
    ];
    temp_count = 2;
  } in
  distinct_homes "parameter prologue writes share a home"
    (Regalloc.allocate params_ir) 0 1;

  (* A leaf function that neither spills nor needs a callee-saved register has
     no reason to touch the stack at all. *)
  let assembly = compile "int main() { int x = 1; int y = 2; return x + y; }" in
  fail_if (contains assembly "addi sp, sp")
    "leaf function still builds a stack frame";
  fail_if (contains assembly "sw ") "leaf function still spills";

  (* Twelve parameters: the last four travel on the stack in both directions. *)
  let assembly =
    compile
      ("int sum(int a,int b,int c,int d,int e,int f,int g,int h,int i,"
       ^ "int j,int k,int l) { return a+b+c+d+e+f+g+h+i+j+k+l; }"
       ^ "int main() { return sum(1,2,3,4,5,6,7,8,9,10,11,12); }")
  in
  fail_if (not (contains assembly "call sum")) "function call was not emitted";
  fail_if
    (not (contains assembly "(sp)" || contains assembly "(s0)"))
    "stack argument area was never addressed";

  (* -opt must not delete observable behaviour: the global is still written on
     every iteration instead of main returning a precomputed literal. *)
  let assembly =
    compile ~opt:true
      "int g = 0; int main() { int i = 0; while (i < 3) { g = g + i; i = i + 1; } return g; }"
  in
  fail_if (not (contains assembly "la t1, g")) "the global store was optimized away";
  fail_if (not (contains assembly "sw ")) "the global store was optimized away";

  (* A comparison that only feeds a branch is folded into the branch, so no
     0/1 value should ever be materialised with slt. *)
  let assembly =
    compile ~opt:true
      "int main() { int i = 0; int s = 0; while (i < 10) { s = s + i; i = i + 1; } return s; }"
  in
  fail_if
    (not (contains assembly "blt" || contains assembly "bge"))
    "loop comparison was not folded into a branch";
  fail_if (contains assembly "  slt ")
    "loop comparison was materialised as a value"
