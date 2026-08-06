let parse source =
  let lexbuf = Lexing.from_string source in
  Frontend.Parser.comp_unit Frontend.Lexer.read lexbuf

let contains haystack needle =
  let n = String.length needle in
  let rec loop i =
    i + n <= String.length haystack
    && (String.sub haystack i n = needle || loop (i + 1))
  in
  n = 0 || loop 0

let compile source =
  let ast = parse source in
  Analysis.Semantic.check ast;
  let program = Backend.Ir.lower ast in
  let path = Filename.temp_file "toyc-codegen" ".s" in
  let out = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out_noerr out)
    (fun () -> Backend.Codegen.emit out program);
  let input = open_in_bin path in
  let assembly =
    Fun.protect
      ~finally:(fun () -> close_in_noerr input)
      (fun () -> really_input_string input (in_channel_length input))
  in
  Sys.remove path;
  assembly

let () =
  (* A value used at a loop header remains live across the whole backedge.
     Textual live intervals alone would incorrectly give t0 and t1 the same
     register, so continue/body code could overwrite the next condition. *)
  let loop_ir : Backend.Ir.func_ir = {
    name = "loop_liveness";
    ret_type = Ast.IntRet;
    params = [];
    locals = [];
    body = [
      Backend.Ir.ILoad (0, Backend.Ir.Imm 5);
      Backend.Ir.ILabel ".Lloop_liveness";
      Backend.Ir.IBranchFalse (0, ".Lloop_liveness_end");
      Backend.Ir.ILoad (1, Backend.Ir.Imm 1);
      Backend.Ir.IStoreGlobal ("sink", 1);
      Backend.Ir.IJump ".Lloop_liveness";
      Backend.Ir.ILabel ".Lloop_liveness_end";
      Backend.Ir.ILoad (2, Backend.Ir.Imm 0);
      Backend.Ir.IReturn (Some 2);
    ];
    temp_count = 3;
  } in
  let locations, _, _ = Backend.Codegen.allocate_registers loop_ir in
  (match Hashtbl.find locations 0, Hashtbl.find locations 1 with
   | Backend.Codegen.Reg a, Backend.Codegen.Reg b when a = b ->
     failwith "loop-invariant value shares a register across the backedge"
   | _ -> ());

  (* A parameter the body never reads needs no home: giving it one costs
     a callee-saved register that the prologue and epilogue then save and
     restore for a value nobody looks at. *)
  let params_ir : Backend.Ir.func_ir = {
    name = "parameter_homes";
    ret_type = Ast.IntRet;
    params = ["live"; "unused"];
    locals = [];
    body = [Backend.Ir.IReturn (Some 0)];
    temp_count = 2;
  } in
  let locations, saved, _ = Backend.Codegen.allocate_registers params_ir in
  if Hashtbl.mem locations 1 then
    failwith "an unread parameter was given a register home";
  if List.length saved > 1 then
    failwith "an unread parameter forced extra callee-saved registers";

  (* Parameters that are read still land in distinct homes: they are all
     written at entry, so sharing one would lose an argument. *)
  let both_used_ir : Backend.Ir.func_ir = {
    name = "both_used";
    ret_type = Ast.IntRet;
    params = ["a"; "b"];
    locals = [];
    body = [
      Backend.Ir.IBinOp (2, Ast.Add, 0, 1);
      Backend.Ir.IReturn (Some 2);
    ];
    temp_count = 3;
  } in
  let locations, _, _ = Backend.Codegen.allocate_registers both_used_ir in
  (match Hashtbl.find locations 0, Hashtbl.find locations 1 with
   | Backend.Codegen.Reg a, Backend.Codegen.Reg b when a = b ->
     failwith "parameter prologue writes share a register home"
   | _ -> ());

  (* Nothing in a leaf function outlives a call, because there are none.
     Everything can therefore live in caller-saved registers, and the
     function needs no frame, no saves and no restores whatsoever. *)
  let assembly =
    compile "int leaf(int a, int b) { return a * b + 7; } int main() { return 0; }"
  in
  if contains assembly "sw s" then
    failwith "a leaf function preserved a callee-saved register it need not use";
  if contains assembly "sw ra" then
    failwith "a leaf function saved a return address it never clobbers";
  if contains assembly "addi sp" then
    failwith "a leaf function needing no stack still built a frame";
  (* Computed straight into the argument registers: codegen used to
     funnel every value through t0/t1/t2 (mv in, compute, mv out), so a
     register-to-register multiply cost four instructions instead of one. *)
  if not (contains assembly "mul a") then
    failwith "leaf arithmetic was not computed in the argument registers";

  (* A value that outlives a call cannot sit in a caller-saved register,
     so it gets a callee-saved one, which then has to be preserved. *)
  let assembly =
    compile
      ("int g(int x) { return x; }"
       ^ "int f(int a) { int keep = a + 5; return g(a) + keep; }"
       ^ "int main() { return 0; }")
  in
  if not (contains assembly "sw s1,") then
    failwith "a value live across a call was not given a preserved register";
  if not (contains assembly "lw s1,") then
    failwith "a preserved register was not restored";
  if not (contains assembly "sw ra,") then
    failwith "a function that calls did not save its return address";

  let assembly =
    compile
      ("int sum(int a,int b,int c,int d,int e,int f,int g,int h,int i,"
       ^ "int j,int k,int l) { return a+b+c+d+e+f+g+h+i+j+k+l; }"
       ^ "int main() { return sum(1,2,3,4,5,6,7,8,9,10,11,12); }")
  in
  if not (contains assembly "call sum") then
    failwith "function call was not emitted";

  (* A power-of-two factor becomes a shift, and the factor itself never
     reaches a register. Only the low 32 bits matter, so this is right
     for negative values too. *)
  let assembly = compile "int f(int a) { return a * 8; } int main() { return 0; }" in
  if not (contains assembly "slli") then
    failwith "multiplying by 8 did not become a shift";
  if contains assembly "mul " then
    failwith "the multiply survived alongside the shift";
  (* the factor itself never appears as an operand; the shift names 3 *)
  if contains assembly ", 8" then
    failwith "the power-of-two factor was still materialized";

  (* A factor that is not a power of two still has to multiply. *)
  let assembly = compile "int f(int a) { return a * 7; } int main() { return 0; }" in
  if not (contains assembly "mul ") then
    failwith "multiplying by 7 should still use mul";

  (* Twenty-five values live at once exceed the twenty-two allocatable
     registers, so the allocator has to spill. Checked through the
     allocator rather than the assembly text: spill slots and saved
     registers are both plain sp offsets now and read the same. *)
  let wide_ir =
    let count = 25 in
    let decls =
      List.init count (fun i -> Printf.sprintf "int v%d = a + %d;" i (i + 1))
    in
    let total =
      String.concat " + " (List.init count (fun i -> Printf.sprintf "v%d" i))
    in
    let ast =
      parse
        (Printf.sprintf "int wide(int a) { %s return %s; } int main() { return 0; }"
           (String.concat " " decls) total)
    in
    Analysis.Semantic.check ast;
    List.find
      (fun (f : Backend.Ir.func_ir) -> f.name = "wide")
      (Backend.Ir.lower ast).funcs
  in
  let _, _, spill_count = Backend.Codegen.allocate_registers wide_ir in
  if spill_count = 0 then
    failwith "register pressure did not exercise spilling";

  (* A comparison feeding the branch right after it becomes one compare-
     and-branch: no slt materializing a 0/1, and no trampoline around an
     unconditional jump. *)
  let assembly = compile "int f(int a, int b) { if (a < b) return 1; return 0; } int main() { return 0; }" in
  if not (contains assembly "bge ") then
    failwith "if (a < b) did not become a single compare-and-branch";
  if contains assembly "slt " then
    failwith "comparison result was materialized instead of folded into the branch";
  if contains assembly ".Lskip" then
    failwith "a short branch still went through the far-branch trampoline";

  (* Each comparison must pick the right inverted mnemonic; a mix-up here
     silently reverses control flow rather than failing to assemble. *)
  let cmp_branch src expected =
    let assembly =
      compile (Printf.sprintf "int f(int a, int b) { if (%s) return 1; return 0; } int main() { return 0; }" src)
    in
    if not (contains assembly (expected ^ " ")) then
      failwith (Printf.sprintf "if (%s) should branch away with %s" src expected)
  in
  cmp_branch "a < b" "bge";
  cmp_branch "a > b" "bge";
  cmp_branch "a <= b" "blt";
  cmp_branch "a >= b" "blt";
  cmp_branch "a == b" "bne";
  cmp_branch "a != b" "beq";

  (* Conditional branches only reach +-4 KiB. Past that the trampoline
     has to come back, or the assembler rejects the branch outright. *)
  let padding =
    String.concat " " (List.init 400 (fun i -> Printf.sprintf "x = x * %d + a;" (i + 2)))
  in
  let assembly =
    compile
      (Printf.sprintf
         "int f(int a, int b) { int x = a; if (a < b) { %s } return x; } int main() { return 0; }"
         padding)
  in
  if not (contains assembly ".Lskip") then
    failwith "an out-of-range branch must fall back to the far-branch sequence"
