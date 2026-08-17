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

(* Mirrors the sequence Optimize.quotient_instrs emits, step for step and with
   the same 32-bit wrapping, so this checks the arithmetic the compiler will
   actually run rather than a restatement of it. *)
let quotient_model ~non_negative d n =
  let magnitude = abs d in
  if Target.is_power_of_two magnitude then begin
    let amount = Target.log2 magnitude in
    let shifted =
      if non_negative then Ir.apply_shift_right_arith n amount
      else
        let sign = Ir.apply_shift_right_arith n 31 in
        let bias = Ir.apply_shift_right_logic sign (32 - amount) in
        Ir.apply_shift_right_arith (Ir.i32 (n + bias)) amount
    in
    if d > 0 then Some shifted else Some (Ir.apply_unary Ast.UMinus shifted)
  end
  else
    match Target.division_magic d with
    | None -> None
    | Some { Target.multiplier; shift } ->
      let high = Ir.apply_mul_high multiplier n in
      let high =
        if d > 0 && multiplier < 0 then Ir.i32 (high + n)
        else if d < 0 && multiplier > 0 then Ir.i32 (high - n)
        else high
      in
      let high = if shift > 0 then Ir.apply_shift_right_arith high shift else high in
      if non_negative && d > 0 then Some high
      else Some (Ir.i32 (high + Ir.apply_shift_right_logic high 31))

let true_quotient d n = Int32.(to_int (div (of_int n) (of_int d)))
let true_remainder d n = Int32.(to_int (rem (of_int n) (of_int d)))

let () =
  (* Division by a constant is replaced by a multiply-and-shift sequence, which
     is only safe if it agrees with the divide instruction on every dividend.
     Sweep the interesting ones: the boundaries, both signs, and a deterministic
     spread in between. *)
  let dividends =
    let rec spread seed count acc =
      if count = 0 then acc
      else
        (* Deterministic LCG, so a failure is always reproducible. *)
        let seed = (seed * 1103515245) + 12345 in
        spread seed (count - 1) (Ir.i32 seed :: acc)
    in
    [ Ir.min_i32; Ir.min_i32 + 1; -2000000000; -1000003; -65536; -12345; -256;
      -7; -3; -2; -1; 0; 1; 2; 3; 7; 256; 12345; 65536; 1000003; 2000000000;
      Ir.max_i32 - 1; Ir.max_i32 ]
    @ spread 1 400 []
  in
  let checked = ref 0 in
  for d = -300 to 300 do
    if d <> 0 && d <> 1 && d <> -1 && d <> Ir.min_i32 then
      List.iter (fun n ->
        (match quotient_model ~non_negative:false d n with
         | None -> ()
         | Some got ->
           incr checked;
           if got <> true_quotient d n then
             failwith
               (Printf.sprintf "constant division wrong: %d / %d gave %d, want %d"
                  n d got (true_quotient d n)));
        (* The shorter sequence used when the dividend is provably non-negative
           has to agree with the general one, not merely be close. *)
        if n >= 0 then begin
          (match quotient_model ~non_negative:true d n with
           | None -> ()
           | Some got ->
             incr checked;
             if got <> true_quotient d n then
               failwith
                 (Printf.sprintf
                    "non-negative division wrong: %d / %d gave %d, want %d" n d got
                    (true_quotient d n)));
          if Target.is_power_of_two (abs d) then begin
            incr checked;
            let got = n land (abs d - 1) in
            if got <> true_remainder d n then
              failwith
                (Printf.sprintf
                   "non-negative masked remainder wrong: %d %% %d gave %d, want %d"
                   n d got (true_remainder d n))
          end
        end
      ) dividends
  done;
  if !checked < 100000 then
    failwith (Printf.sprintf "division sweep only checked %d cases" !checked);

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
     0/1 value should ever be materialised with slt.  The bound is a global so
     that the loop survives to be branched over at all: with a literal bound the
     whole thing has a closed form and disappears. *)
  let assembly =
    compile ~opt:true
      ("int limit = 10; int main() { int i = 0; int s = 0; "
       ^ "while (i < limit) { s = s + i; i = i + 1; } return s; }")
  in
  fail_if
    (not (contains assembly "blt" || contains assembly "bge"))
    "loop comparison was not folded into a branch";
  fail_if (contains assembly "  slt ")
    "loop comparison was materialised as a value";

  (* Global promotion can turn a loop that writes a global into one that only
     computes, at which point the closed form applies and the loop collapses to
     its write-back.  The store itself still has to be there: what the memory
     ends up holding is observable, only the intermediate values are not. *)
  let assembly =
    compile ~opt:true
      ("int g = 0; int main() { int i = 0; int s = 0; "
       ^ "while (i < 1000) { s = s + i; g = s; i = i + 1; } return s; }")
  in
  fail_if (not (contains assembly "la t1, g")) "closed-form rewrite dropped a global store";
  fail_if (not (contains assembly "sw ")) "closed-form rewrite dropped a global store";

  (* A call is not a value the analysis can evolve, so a loop containing one
     keeps running however arithmetic the rest of its body looks. *)
  let assembly =
    compile ~opt:true
      ("int fact(int n) { if (n <= 1) return 1; return n * fact(n - 1); } "
       ^ "int main() { int i = 1; int s = 0; "
       ^ "while (i < 100) { s = s + fact(i); i = i + 1; } return s; }")
  in
  fail_if (not (contains assembly "call fact")) "the call was optimized away";
  fail_if
    (not (contains assembly "blt" || contains assembly "bge"))
    "closed-form rewrite deleted a loop containing a call";

  (* An unrolled body still runs the loop; the counter just advances by the
     whole factor between tests. *)
  let assembly =
    compile ~opt:true
      ("int g = 0; int main() { int i = 0; "
       ^ "while (i < 4000) { g = g + i; i = i + 1; } return g; }")
  in
  fail_if
    (not (contains assembly "blt" || contains assembly "bge"))
    "unrolled loop lost its back branch"
