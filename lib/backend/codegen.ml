(** RISC-V32 code generation from IR
 *
 * Calling convention (matches standard RISC-V ILP32):
 *   - a0-a7: argument registers (first 8 args)
 *   - a0: return value
 *   - ra: return address (caller-saved)
 *   - sp: stack pointer (16-byte aligned)
 *   - s0/fp: frame pointer (callee-saved)
 *   - t0-t6: caller-saved temporaries
 *
 * Stack frame layout (growing downward):
 *   high address
 *   +-------------------+
 *   | caller's frame    |
 *   +-------------------+ <- old sp = s0
 *   | saved ra          |  s0 - 4
 *   | saved s0 (fp)     |  s0 - 8
 *   | saved s1-s11      |  only registers used by this function
 *   | alignment padding |
 *   | temp spill slots  |  only when register pressure exceeds 11
 *   +-------------------+ <- sp (16-byte aligned)
 *   low address
 *
 * Register allocation strategy:
 *   CFG liveness analysis plus interference-graph coloring. Values are kept
 *   in callee-saved registers s1-s11 across calls; only excess values spill.
 *   Spill slots use s0-relative addressing so call-time sp adjustments do
 *   not invalidate their addresses.
 *)

open Ir
open Ast

module IntSet = Set.Make (Int)

type emit_ctx = {
  out : Buffer.t;
  func : func_ir;
  mutable frame_size : int;
  temp_loc : (int, temp_loc) Hashtbl.t;
  used_regs : string list;
  branch_cnt : int ref;
  (* estimated instruction offset of each label, and of the instruction
     being emitted, used to tell whether a conditional branch can reach
     its target directly *)
  label_off : (string, int) Hashtbl.t;
  mutable cur_off : int;
  (* constants folded into instruction immediates, so never materialized *)
  imm_temps : (int, int) Hashtbl.t;
}

and temp_loc = Reg of string | Spill of int

let buf_emit ctx fmt = Printf.bprintf ctx.out fmt

let align16 n = (n + 15) land (lnot 15)

let set_of_list xs =
  List.fold_left (fun set x -> IntSet.add x set) IntSet.empty xs

let instr_defs_uses = function
  | ILoad (d, Imm _) | ILoad (d, Name _) | ILoadGlobal (d, _) ->
    IntSet.singleton d, IntSet.empty
  | ILoad (d, Temp s) | IUnaryOp (d, _, s) ->
    IntSet.singleton d, IntSet.singleton s
  | IStoreGlobal (_, s) | IBranchTrue (s, _) | IBranchFalse (s, _) ->
    IntSet.empty, IntSet.singleton s
  | IBinOp (d, _, l, r) ->
    IntSet.singleton d, set_of_list [l; r]
  | ICall (d, _, args) ->
    IntSet.singleton d, set_of_list args
  | ICallVoid (_, args) ->
    IntSet.empty, set_of_list args
  | IReturn (Some s) ->
    IntSet.empty, IntSet.singleton s
  | ILabel _ | IJump _ | IReturn None | IComment _ ->
    IntSet.empty, IntSet.empty

let allocate_registers (func : func_ir) =
  let body : instr array = Array.of_list func.body in
  let count = Array.length body in
  let labels = Hashtbl.create 16 in
  Array.iteri (fun i instr ->
    match instr with
    | ILabel label -> Hashtbl.replace labels label i
    | _ -> ()
  ) body;
  let next i = if i + 1 < count then [i + 1] else [] in
  let successors = Array.init count (fun i ->
    match body.(i) with
    | IJump label -> [Hashtbl.find labels label]
    | IBranchTrue (_, label) | IBranchFalse (_, label) ->
      Hashtbl.find labels label :: next i
    | IReturn _ -> []
    | _ -> next i
  ) in
  let defs_uses = Array.map instr_defs_uses body in
  let live_in = Array.make count IntSet.empty in
  let live_out = Array.make count IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = count - 1 downto 0 do
      let new_out = List.fold_left (fun set succ ->
        IntSet.union set live_in.(succ)
      ) IntSet.empty successors.(i) in
      let defs, uses = defs_uses.(i) in
      let new_in = IntSet.union uses (IntSet.diff new_out defs) in
      if not (IntSet.equal new_out live_out.(i)) then begin
        live_out.(i) <- new_out;
        changed := true
      end;
      if not (IntSet.equal new_in live_in.(i)) then begin
        live_in.(i) <- new_in;
        changed := true
      end
    done
  done;
  let adjacency = Array.make func.temp_count IntSet.empty in
  let add_edge a b =
    if a <> b && a >= 0 && b >= 0
       && a < func.temp_count && b < func.temp_count then begin
      adjacency.(a) <- IntSet.add b adjacency.(a);
      adjacency.(b) <- IntSet.add a adjacency.(b)
    end
  in
  let add_clique live =
    IntSet.iter (fun a -> IntSet.iter (fun b -> add_edge a b) live) live
  in
  Array.iter add_clique live_in;
  Array.iter add_clique live_out;
  (* Code generation still writes dead destinations, so they must not share
     a home with values that remain live after that instruction. *)
  Array.iteri (fun i (defs, _) ->
    IntSet.iter (fun def ->
      IntSet.iter (fun live -> add_edge def live) live_out.(i)
    ) defs
  ) defs_uses;
  (* Every parameter is copied to its home in the prologue, including unused
     parameters. Keep those entry writes from overwriting one another. *)
  let param_temps =
    List.init (List.length func.params) (fun i -> i) |> set_of_list
  in
  add_clique param_temps;
  let registers = [| "s1"; "s2"; "s3"; "s4"; "s5"; "s6";
                     "s7"; "s8"; "s9"; "s10"; "s11" |] in
  let order = List.init func.temp_count (fun i -> i) in
  let order = List.sort (fun a b ->
    compare (IntSet.cardinal adjacency.(b)) (IntSet.cardinal adjacency.(a))
  ) order in
  let colors = Array.make func.temp_count None in
  let locations = Hashtbl.create func.temp_count in
  let spill_count = ref 0 in
  List.iter (fun temp ->
    let unavailable = IntSet.fold (fun neighbor set ->
      match colors.(neighbor) with
      | Some color -> IntSet.add color set
      | None -> set
    ) adjacency.(temp) IntSet.empty in
    let rec choose color =
      if color = Array.length registers then None
      else if IntSet.mem color unavailable then choose (color + 1)
      else Some color
    in
    match choose 0 with
    | Some color -> colors.(temp) <- Some color
    | None ->
      Hashtbl.add locations temp (Spill !spill_count);
      incr spill_count
  ) order;
  Array.iteri (fun temp color ->
    match color with
    | Some index -> Hashtbl.add locations temp (Reg registers.(index))
    | None -> ()
  ) colors;
  let used_regs = Array.to_list registers |> List.filteri (fun index _ ->
    Array.exists (fun color -> color = Some index) colors
  ) in
  locations, used_regs, !spill_count

let immediate_fits n = n >= -2048 && n <= 2047

(* Constants small enough to ride along inside an instruction, and read
   only by instructions that have an immediate form. These need no
   register at all: the load disappears and every use folds the value in.
   addi is the only immediate form used here, so a candidate survives
   only where it is an addend of an add, or the subtrahend of a sub
   (folded as its negation); any other reader forces it into a register. *)
let immediate_temps (body : instr list) =
  let candidates = Hashtbl.create 16 in
  let def_count = Hashtbl.create 16 in
  List.iter (fun instr ->
    let defs, _ = instr_defs_uses instr in
    IntSet.iter (fun d ->
      Hashtbl.replace def_count d
        (1 + Option.value ~default:0 (Hashtbl.find_opt def_count d))
    ) defs
  ) body;
  List.iter (fun instr ->
    match instr with
    | ILoad (t, Imm n) when immediate_fits n -> Hashtbl.replace candidates t n
    | _ -> ()
  ) body;
  (* a temp written more than once has no single value to fold *)
  Hashtbl.iter (fun t _ ->
    if Hashtbl.find_opt def_count t <> Some 1 then Hashtbl.remove candidates t
  ) (Hashtbl.copy candidates);
  let is_const t = Hashtbl.mem candidates t in
  List.iter (fun instr ->
    let allowed =
      match instr with
      | ILoad (_, Imm _) -> []
      | IBinOp (_, Add, a, b) ->
        (* only one side can become the immediate *)
        if is_const a && is_const b then []
        else if is_const b then [b]
        else if is_const a then [a]
        else []
      | IBinOp (_, Sub, a, b) ->
        if is_const b && not (is_const a) then [b] else []
      | _ -> []
    in
    let _, uses = instr_defs_uses instr in
    IntSet.iter (fun u ->
      if not (List.mem u allowed) then Hashtbl.remove candidates u
    ) uses
  ) body;
  (* a subtrahend folds as addi with the negation, which must fit too *)
  List.iter (fun instr ->
    match instr with
    | IBinOp (_, Sub, _, b) ->
      (match Hashtbl.find_opt candidates b with
       | Some n when not (immediate_fits (- n)) -> Hashtbl.remove candidates b
       | _ -> ())
    | _ -> ()
  ) body;
  candidates

(* Body as the register allocator should see it: folded constants no
   longer have a definition, and the adds that absorb them read one
   operand instead of two. UPlus stands in because it carries exactly the
   def/use shape of the addi that will be emitted. *)
let allocation_view imm_temps (body : instr list) =
  List.filter_map (fun instr ->
    match instr with
    | ILoad (t, Imm _) when Hashtbl.mem imm_temps t -> None
    | IBinOp (d, Add, a, b) when Hashtbl.mem imm_temps b -> Some (IUnaryOp (d, UPlus, a))
    | IBinOp (d, Add, a, b) when Hashtbl.mem imm_temps a -> Some (IUnaryOp (d, UPlus, b))
    | IBinOp (d, Sub, a, b) when Hashtbl.mem imm_temps b -> Some (IUnaryOp (d, UPlus, a))
    | _ -> Some instr
  ) body

let compute_frame (func : func_ir) =
  let imm_temps = immediate_temps func.body in
  let alloc_func = { func with body = allocation_view imm_temps func.body } in
  let temp_loc, used_regs, spill_count = allocate_registers alloc_func in
  let saved_slots = 2 + List.length used_regs in
  let frame_size = align16 ((saved_slots + spill_count) * 4) in
  (frame_size, temp_loc, used_regs, imm_temps)

let emit_addi ctx rd rs imm =
  if imm >= -2048 && imm <= 2047 then
    buf_emit ctx "  addi %s, %s, %d\n" rd rs imm
  else begin
    buf_emit ctx "  li t3, %d\n" imm;
    buf_emit ctx "  add %s, %s, t3\n" rd rs
  end

let emit_lw ctx reg base offset =
  if offset >= -2048 && offset <= 2047 then
    buf_emit ctx "  lw %s, %d(%s)\n" reg offset base
  else begin
    buf_emit ctx "  li t3, %d\n" offset;
    buf_emit ctx "  add t3, %s, t3\n" base;
    buf_emit ctx "  lw %s, 0(t3)\n" reg
  end

let emit_sw ctx reg base offset =
  if offset >= -2048 && offset <= 2047 then
    buf_emit ctx "  sw %s, %d(%s)\n" reg offset base
  else begin
    buf_emit ctx "  li t3, %d\n" offset;
    buf_emit ctx "  add t3, %s, t3\n" base;
    buf_emit ctx "  sw %s, 0(t3)\n" reg
  end

let load_temp ctx reg t =
  match Hashtbl.find ctx.temp_loc t with
  | Reg src -> if src <> reg then buf_emit ctx "  mv %s, %s\n" reg src
  | Spill slot -> emit_lw ctx reg "s0" ((slot * 4) - ctx.frame_size)

let store_temp ctx reg t =
  match Hashtbl.find ctx.temp_loc t with
  | Reg dst -> if dst <> reg then buf_emit ctx "  mv %s, %s\n" dst reg
  | Spill slot -> emit_sw ctx reg "s0" ((slot * 4) - ctx.frame_size)

(* Register already holding temp [t]. A register-allocated temp is read in
   place; only a spilled one costs a load into [scratch]. Operating on the
   allocated register directly is what removes the mv-in/mv-out pair that
   used to bracket every single computation. *)
let src_reg ctx t scratch =
  match Hashtbl.find ctx.temp_loc t with
  | Reg r -> r
  | Spill slot ->
    emit_lw ctx scratch "s0" ((slot * 4) - ctx.frame_size);
    scratch

(* Register to compute temp [t] into, plus the store-back that a spilled
   temp needs once the value is there. *)
let dst_reg ctx t scratch =
  match Hashtbl.find ctx.temp_loc t with
  | Reg r -> (r, fun () -> ())
  | Spill slot ->
    (scratch, fun () -> emit_sw ctx scratch "s0" ((slot * 4) - ctx.frame_size))

let emit_global_addr ctx reg name =
  buf_emit ctx "  la %s, %s\n" reg name

let emit_prologue ctx =
  emit_addi ctx "sp" "sp" (- ctx.frame_size);
  emit_sw ctx "ra" "sp" (ctx.frame_size - 4);
  emit_sw ctx "s0" "sp" (ctx.frame_size - 8);
  List.iteri (fun i reg ->
    emit_sw ctx reg "sp" (ctx.frame_size - 12 - (i * 4))
  ) ctx.used_regs;
  emit_addi ctx "s0" "sp" ctx.frame_size

let emit_epilogue ctx =
  List.iteri (fun i reg ->
    emit_lw ctx reg "sp" (ctx.frame_size - 12 - (i * 4))
  ) ctx.used_regs;
  emit_lw ctx "ra" "sp" (ctx.frame_size - 4);
  emit_lw ctx "s0" "sp" (ctx.frame_size - 8);
  emit_addi ctx "sp" "sp" ctx.frame_size;
  buf_emit ctx "  ret\n"

let emit_binop ctx dst op lhs rhs =
  let a = src_reg ctx lhs "t0" in
  let b = src_reg ctx rhs "t1" in
  let d, finish = dst_reg ctx dst "t2" in
  (* Reading both operands and writing the result in one instruction is
     safe even when [d] aliases [a] or [b]. The two-step forms below only
     re-read [d] after it already holds the intermediate result. *)
  (match op with
   | Add -> buf_emit ctx "  add %s, %s, %s\n" d a b
   | Sub -> buf_emit ctx "  sub %s, %s, %s\n" d a b
   | Mul -> buf_emit ctx "  mul %s, %s, %s\n" d a b
   | Div -> buf_emit ctx "  div %s, %s, %s\n" d a b
   | Mod -> buf_emit ctx "  rem %s, %s, %s\n" d a b
   | Lt ->  buf_emit ctx "  slt %s, %s, %s\n" d a b
   | Gt ->  buf_emit ctx "  slt %s, %s, %s\n" d b a
   | Le ->
     buf_emit ctx "  slt %s, %s, %s\n" d b a;
     buf_emit ctx "  xori %s, %s, 1\n" d d
   | Ge ->
     buf_emit ctx "  slt %s, %s, %s\n" d a b;
     buf_emit ctx "  xori %s, %s, 1\n" d d
   | Eq ->
     buf_emit ctx "  sub %s, %s, %s\n" d a b;
     buf_emit ctx "  seqz %s, %s\n" d d
   | Ne ->
     buf_emit ctx "  sub %s, %s, %s\n" d a b;
     buf_emit ctx "  snez %s, %s\n" d d
   | And ->
     (* both operands must be normalized to 0/1 before the result is
        written, so these go through scratch: writing [d] first could
        clobber an operand it aliases *)
     buf_emit ctx "  snez t0, %s\n" a;
     buf_emit ctx "  snez t1, %s\n" b;
     buf_emit ctx "  and %s, t0, t1\n" d
   | Or ->
     buf_emit ctx "  or t0, %s, %s\n" a b;
     buf_emit ctx "  snez %s, t0\n" d);
  finish ()

let emit_unaryop ctx dst op src =
  let s = src_reg ctx src "t0" in
  let d, finish = dst_reg ctx dst "t2" in
  (match op with
   | UPlus -> if d <> s then buf_emit ctx "  mv %s, %s\n" d s
   | UMinus -> buf_emit ctx "  neg %s, %s\n" d s
   | Not ->  buf_emit ctx "  seqz %s, %s\n" d s);
  finish ()

(* A comparison feeding straight into a branch becomes a single compare-
   and-branch, dropping both the slt and the test of its 0/1 result.
   [invert] selects the IBranchFalse sense (branch when the comparison
   does not hold). *)
let emit_fused_branch ctx op lhs rhs lbl ~invert =
  let a = src_reg ctx lhs "t0" in
  let b = src_reg ctx rhs "t1" in
  let mnemonic, x, y =
    match op, invert with
    | Lt, false -> "blt", a, b
    | Lt, true  -> "bge", a, b
    | Gt, false -> "blt", b, a
    | Gt, true  -> "bge", b, a
    | Le, false -> "bge", b, a
    | Le, true  -> "blt", b, a
    | Ge, false -> "bge", a, b
    | Ge, true  -> "blt", a, b
    | Eq, false -> "beq", a, b
    | Eq, true  -> "bne", a, b
    | Ne, false -> "bne", a, b
    | Ne, true  -> "beq", a, b
    | (Add | Sub | Mul | Div | Mod | And | Or), _ ->
      invalid_arg "emit_fused_branch: not a comparison"
  in
  buf_emit ctx "  %s %s, %s, %s\n" mnemonic x y lbl

let emit_call ctx dst_opt name args =
  let nargs = List.length args in
  let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |] in
  let stack_args = if nargs > 8 then nargs - 8 else 0 in
  if stack_args > 0 then begin
    let extra = align16 (stack_args * 4) in
    emit_addi ctx "sp" "sp" (- extra)
  end;
  List.iteri (fun i t ->
    if i < 8 then begin
      load_temp ctx arg_regs.(i) t
    end else begin
      load_temp ctx "t0" t;
      emit_sw ctx "t0" "sp" ((i - 8) * 4)
    end
  ) args;
  buf_emit ctx "  call %s\n" name;
  if stack_args > 0 then begin
    let extra = align16 (stack_args * 4) in
    emit_addi ctx "sp" "sp" extra
  end;
  (match dst_opt with
   | Some dst -> store_temp ctx "a0" dst
   | None -> ())

(* A conditional branch reaches +-4 KiB, i.e. +-1024 instructions. The
   offsets below are upper-bound estimates, so staying well inside that
   limit keeps the direct form safe; anything further falls back to the
   inverted-branch-over-jump sequence, which has unlimited range. *)
let branch_reach_limit = 800

let branch_reaches ctx lbl =
  match Hashtbl.find_opt ctx.label_off lbl with
  | Some target -> abs (target - ctx.cur_off) < branch_reach_limit
  | None -> false

(* Upper bound on the machine instructions one IR instruction expands to.
   Only used for the reachability estimate above; over-estimating merely
   gives up a direct branch, it can never produce wrong code. *)
let max_expansion used_reg_count = function
  | ILabel _ | IComment _ -> 0
  | IJump _ -> 1
  | ILoad (_, Imm _) | ILoad (_, Temp _) -> 4
  | ILoad (_, Name _) | ILoadGlobal _ | IStoreGlobal _ -> 7
  | IBinOp _ -> 12
  | IUnaryOp _ -> 9
  | IBranchTrue _ | IBranchFalse _ -> 7
  | ICall (_, _, args) | ICallVoid (_, args) -> 12 + (3 * List.length args)
  | IReturn _ -> 12 + (3 * used_reg_count)

let instr_offsets used_reg_count (body : instr array) =
  let offsets = Array.make (Array.length body + 1) 0 in
  Array.iteri (fun i instr ->
    offsets.(i + 1) <- offsets.(i) + max_expansion used_reg_count instr
  ) body;
  offsets

let label_offsets offsets (body : instr array) =
  let table = Hashtbl.create 16 in
  Array.iteri (fun i instr ->
    match instr with
    | ILabel l -> Hashtbl.replace table l offsets.(i)
    | _ -> ()
  ) body;
  table

(* How many instructions read each temp, so a comparison whose result is
   consumed only by the branch right after it can be fused away. *)
let use_counts (body : instr array) =
  let counts = Hashtbl.create 64 in
  Array.iter (fun instr ->
    let _, uses = instr_defs_uses instr in
    IntSet.iter (fun t ->
      Hashtbl.replace counts t (1 + Option.value ~default:0 (Hashtbl.find_opt counts t))
    ) uses
  ) body;
  counts

let emit_cond_branch ctx t lbl ~invert =
  let r = src_reg ctx t "t0" in
  if branch_reaches ctx lbl then
    buf_emit ctx "  %s %s, %s\n" (if invert then "beqz" else "bnez") r lbl
  else begin
    let n = !(ctx.branch_cnt) in
    ctx.branch_cnt := n + 1;
    let skip = Printf.sprintf ".Lskip%d" n in
    buf_emit ctx "  %s %s, %s\n" (if invert then "bnez" else "beqz") r skip;
    buf_emit ctx "  j %s\n" lbl;
    buf_emit ctx "%s:\n" skip
  end

(* dst = src + n, the folded form of a load-constant plus an add *)
let emit_addi_temp ctx dst src n =
  let s = src_reg ctx src "t0" in
  let d, finish = dst_reg ctx dst "t2" in
  buf_emit ctx "  addi %s, %s, %d\n" d s n;
  finish ()

let emit_instr ctx instr =
  match instr with
  (* a constant that every reader folds in is never materialized *)
  | ILoad (dst, Imm _) when Hashtbl.mem ctx.imm_temps dst -> ()
  | IBinOp (dst, Add, a, b) when Hashtbl.mem ctx.imm_temps b ->
    emit_addi_temp ctx dst a (Hashtbl.find ctx.imm_temps b)
  | IBinOp (dst, Add, a, b) when Hashtbl.mem ctx.imm_temps a ->
    emit_addi_temp ctx dst b (Hashtbl.find ctx.imm_temps a)
  | IBinOp (dst, Sub, a, b) when Hashtbl.mem ctx.imm_temps b ->
    emit_addi_temp ctx dst a (- (Hashtbl.find ctx.imm_temps b))
  | ILoad (dst, Imm n) ->
    let d, finish = dst_reg ctx dst "t0" in
    buf_emit ctx "  li %s, %d\n" d n;
    finish ()
  | ILoad (dst, Temp src) ->
    let s = src_reg ctx src "t0" in
    (match Hashtbl.find ctx.temp_loc dst with
     | Reg d -> if d <> s then buf_emit ctx "  mv %s, %s\n" d s
     | Spill slot -> emit_sw ctx s "s0" ((slot * 4) - ctx.frame_size))
  | ILoad (dst, Name name) | ILoadGlobal (dst, name) ->
    let d, finish = dst_reg ctx dst "t0" in
    emit_global_addr ctx "t1" name;
    buf_emit ctx "  lw %s, 0(t1)\n" d;
    finish ()
  | IStoreGlobal (name, src) ->
    let s = src_reg ctx src "t0" in
    emit_global_addr ctx "t1" name;
    buf_emit ctx "  sw %s, 0(t1)\n" s
  | IBinOp (dst, op, lhs, rhs) ->
    emit_binop ctx dst op lhs rhs
  | IUnaryOp (dst, op, src) ->
    emit_unaryop ctx dst op src
  | ICall (dst, name, args) ->
    emit_call ctx (Some dst) name args
  | ICallVoid (name, args) ->
    emit_call ctx None name args
  | ILabel lbl ->
    buf_emit ctx "%s:\n" lbl
  | IJump lbl ->
    buf_emit ctx "  j %s\n" lbl
  | IBranchTrue (t, lbl) -> emit_cond_branch ctx t lbl ~invert:false
  | IBranchFalse (t, lbl) -> emit_cond_branch ctx t lbl ~invert:true
  | IReturn opt ->
    (match opt with
     | Some t -> load_temp ctx "a0" t
     | None -> ());
    emit_epilogue ctx
  | IComment s ->
    buf_emit ctx "  # %s\n" s

let is_comparison = function
  | Lt | Gt | Le | Ge | Eq | Ne -> true
  | Add | Sub | Mul | Div | Mod | And | Or -> false

let emit_func ctx func =
  let (frame_size, temp_loc, used_regs, imm_temps) = compute_frame func in
  let body = Array.of_list func.body in
  let offsets = instr_offsets (List.length used_regs) body in
  let label_off = label_offsets offsets body in
  let ctx =
    { ctx with
      func; frame_size; temp_loc; used_regs; label_off; cur_off = 0; imm_temps }
  in
  buf_emit ctx "\n  .text\n";
  buf_emit ctx "  .globl %s\n" func.name;
  buf_emit ctx "%s:\n" func.name;
  emit_prologue ctx;
  let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |] in
  List.iteri (fun i _p ->
    if i < 8 then
      store_temp ctx arg_regs.(i) i
    else begin
      emit_lw ctx "t0" "s0" ((i - 8) * 4);
      store_temp ctx "t0" i
    end
  ) func.params;
  let uses = use_counts body in
  let count = Array.length body in
  let i = ref 0 in
  while !i < count do
    ctx.cur_off <- offsets.(!i);
    let fused =
      (* a comparison whose only reader is the branch immediately after it *)
      if !i + 1 >= count then None
      else
        match body.(!i), body.(!i + 1) with
        | IBinOp (t, op, lhs, rhs), IBranchTrue (t', lbl)
          when t = t' && is_comparison op
               && Hashtbl.find_opt uses t = Some 1
               && branch_reaches ctx lbl ->
          Some (op, lhs, rhs, lbl, false)
        | IBinOp (t, op, lhs, rhs), IBranchFalse (t', lbl)
          when t = t' && is_comparison op
               && Hashtbl.find_opt uses t = Some 1
               && branch_reaches ctx lbl ->
          Some (op, lhs, rhs, lbl, true)
        | _ -> None
    in
    match fused with
    | Some (op, lhs, rhs, lbl, invert) ->
      emit_fused_branch ctx op lhs rhs lbl ~invert;
      i := !i + 2
    | None ->
      emit_instr ctx body.(!i);
      incr i
  done

let emit_globals ctx globals =
  let has_data = List.exists (fun g ->
    match g with GVar _ -> true | GConst _ -> true) globals in
  if has_data then begin
    buf_emit ctx "  .data\n";
    List.iter (fun g ->
      match g with
      | GConst (name, value) ->
        buf_emit ctx "  .globl %s\n" name;
        buf_emit ctx "  .align 2\n";
        buf_emit ctx "%s:\n" name;
        buf_emit ctx "  .word %d\n" value
      | GVar (name, value) ->
        buf_emit ctx "  .globl %s\n" name;
        buf_emit ctx "  .align 2\n";
        buf_emit ctx "%s:\n" name;
        buf_emit ctx "  .word %d\n" value
    ) globals
  end

let emit (out : out_channel) (prog : program) : unit =
  let ctx = {
    out = Buffer.create 4096;
    func = { name = ""; ret_type = VoidRet; params = []; locals = [];
             body = []; temp_count = 0 };
    frame_size = 0;
    temp_loc = Hashtbl.create 0;
    used_regs = [];
    branch_cnt = ref 0;
    label_off = Hashtbl.create 0;
    cur_off = 0;
    imm_temps = Hashtbl.create 0;
  } in
  emit_globals ctx prog.globals;
  List.iter (emit_func ctx) prog.funcs;
  Buffer.output_buffer out ctx.out
