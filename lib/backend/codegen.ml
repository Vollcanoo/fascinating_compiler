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
  (* spill slots are addressed from sp, which never moves inside a body *)
  mutable spill_base : int;
  mutable leaf : bool;
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
  (* Only temps the body actually mentions need a home. Optimization
     deletes instructions, and a temp whose every mention is gone would
     otherwise still be colored -- reserving a callee-saved register that
     the prologue and epilogue then save and restore for nothing. *)
  let mentioned =
    Array.fold_left (fun set (defs, uses) ->
      IntSet.union set (IntSet.union defs uses)
    ) IntSet.empty defs_uses
  in
  (* Every parameter still mentioned is copied to its home in the
     prologue. Keep those entry writes from overwriting one another. *)
  let param_temps =
    List.init (List.length func.params) (fun i -> i)
    |> List.filter (fun t -> IntSet.mem t mentioned)
    |> set_of_list
  in
  add_clique param_temps;
  (* A call destroys every caller-saved register, so a value that is live
     across one has to sit in a callee-saved register (or spill). Values
     that die before any call can use caller-saved registers instead,
     which cost nothing to save: a leaf function needs no frame at all. *)
  let across_calls =
    let set = ref IntSet.empty in
    Array.iteri (fun i instr ->
      match instr with
      (* The result is produced by the call, not carried across it: it
         arrives in a0 and may stay in a caller-saved register. *)
      | ICall (d, _, _) -> set := IntSet.union !set (IntSet.remove d live_out.(i))
      | ICallVoid _ -> set := IntSet.union !set live_out.(i)
      | _ -> ()
    ) body;
    !set
  in
  let callee_saved = [| "s1"; "s2"; "s3"; "s4"; "s5"; "s6";
                        "s7"; "s8"; "s9"; "s10"; "s11" |] in
  (* t0-t3 stay reserved as codegen scratch. *)
  let caller_saved = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
                        "t4"; "t5"; "t6" |] in
  let callee_count = Array.length callee_saved in
  let register_of_color c =
    if c < callee_count then callee_saved.(c)
    else caller_saved.(c - callee_count)
  in
  let caller_colors =
    List.init (Array.length caller_saved) (fun i -> callee_count + i)
  in
  let callee_colors = List.init callee_count (fun i -> i) in
  let param_count = List.length func.params in
  let order =
    List.init func.temp_count (fun i -> i)
    |> List.filter (fun t -> IntSet.mem t mentioned)
  in
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
    let candidates =
      if IntSet.mem temp across_calls then callee_colors
      else
        (* a parameter that can stay where it arrived needs no entry copy *)
        let preferred =
          if temp < param_count && temp < 8 then [ callee_count + temp ] else []
        in
        preferred @ caller_colors @ callee_colors
    in
    let rec choose = function
      | [] -> None
      | c :: rest -> if IntSet.mem c unavailable then choose rest else Some c
    in
    match choose candidates with
    | Some color -> colors.(temp) <- Some color
    | None ->
      Hashtbl.add locations temp (Spill !spill_count);
      incr spill_count
  ) order;
  Array.iteri (fun temp color ->
    match color with
    | Some index -> Hashtbl.add locations temp (Reg (register_of_color index))
    | None -> ()
  ) colors;
  (* only callee-saved registers have to be preserved by this function *)
  let used_regs = Array.to_list callee_saved |> List.filteri (fun index _ ->
    Array.exists (fun color -> color = Some index) colors
  ) in
  locations, used_regs, !spill_count

let immediate_fits n = n >= -2048 && n <= 2047

(* Multiplying by a power of two is a left shift, which costs one cycle
   against several for mul. The low 32 bits are identical either way, so
   this holds for negative values too. *)
let shift_for_multiply n =
  if n <= 0 then None
  else
    let rec bit k = if k >= 31 then None else if 1 lsl k = n then Some k else bit (k + 1) in
    bit 1

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
      | IBinOp (_, Mul, a, b) ->
        (* a power-of-two factor becomes the shift amount *)
        let shiftable t =
          match Hashtbl.find_opt candidates t with
          | Some n -> shift_for_multiply n <> None
          | None -> false
        in
        if is_const a && is_const b then []
        else if shiftable b then [b]
        else if shiftable a then [a]
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
    | IBinOp (d, Mul, a, b) when Hashtbl.mem imm_temps b -> Some (IUnaryOp (d, UPlus, a))
    | IBinOp (d, Mul, a, b) when Hashtbl.mem imm_temps a -> Some (IUnaryOp (d, UPlus, b))
    | _ -> Some instr
  ) body

(* Words of outgoing arguments the widest call in this function needs.
   Reserving that area up front is what lets sp stay put for the whole
   body, which in turn is what makes sp-relative spill slots work and
   removes the need for a frame pointer. *)
let outgoing_words (body : instr list) =
  List.fold_left (fun acc instr ->
    match instr with
    | ICall (_, _, args) | ICallVoid (_, args) ->
      max acc (max 0 (List.length args - 8))
    | _ -> acc
  ) 0 body

let is_leaf (body : instr list) =
  not (List.exists (function ICall _ | ICallVoid _ -> true | _ -> false) body)

type frame = {
  size : int;
  locs : (int, temp_loc) Hashtbl.t;
  saved : string list;
  immediates : (int, int) Hashtbl.t;
  leaf : bool;
  (* byte offset from sp of spill slot 0 *)
  spill_base : int;
}

let compute_frame (func : func_ir) =
  let immediates = immediate_temps func.body in
  let alloc_func = { func with body = allocation_view immediates func.body } in
  let locs, saved, spill_count = allocate_registers alloc_func in
  let leaf = is_leaf func.body in
  (* a leaf calls nothing, so it neither passes arguments on the stack
     nor has a return address worth preserving *)
  let outgoing = if leaf then 0 else outgoing_words func.body in
  let ra_words = if leaf then 0 else 1 in
  let words = outgoing + spill_count + List.length saved + ra_words in
  { size = align16 (words * 4);
    locs;
    saved;
    immediates;
    leaf;
    spill_base = outgoing * 4 }

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

let spill_offset (ctx : emit_ctx) slot = ctx.spill_base + (slot * 4)

let load_temp ctx reg t =
  match Hashtbl.find ctx.temp_loc t with
  | Reg src -> if src <> reg then buf_emit ctx "  mv %s, %s\n" reg src
  | Spill slot -> emit_lw ctx reg "sp" (spill_offset ctx slot)

let store_temp ctx reg t =
  match Hashtbl.find ctx.temp_loc t with
  | Reg dst -> if dst <> reg then buf_emit ctx "  mv %s, %s\n" dst reg
  | Spill slot -> emit_sw ctx reg "sp" (spill_offset ctx slot)

(* Register already holding temp [t]. A register-allocated temp is read in
   place; only a spilled one costs a load into [scratch]. Operating on the
   allocated register directly is what removes the mv-in/mv-out pair that
   used to bracket every single computation. *)
let src_reg ctx t scratch =
  match Hashtbl.find ctx.temp_loc t with
  | Reg r -> r
  | Spill slot ->
    emit_lw ctx scratch "sp" (spill_offset ctx slot);
    scratch

(* Register to compute temp [t] into, plus the store-back that a spilled
   temp needs once the value is there. *)
let dst_reg ctx t scratch =
  match Hashtbl.find ctx.temp_loc t with
  | Reg r -> (r, fun () -> ())
  | Spill slot ->
    (scratch, fun () -> emit_sw ctx scratch "sp" (spill_offset ctx slot))

let emit_global_addr ctx reg name =
  buf_emit ctx "  la %s, %s\n" reg name

(* Saved registers sit at the top of the frame, under the return address
   when there is one. Everything is sp-relative: reserving the outgoing
   argument area up front keeps sp fixed for the whole body, so no frame
   pointer is needed and s0 is never touched. *)
let saved_offset (ctx : emit_ctx) i =
  let ra_words = if ctx.leaf then 0 else 1 in
  ctx.frame_size - (4 * (ra_words + i + 1))

let emit_prologue (ctx : emit_ctx) =
  if ctx.frame_size > 0 then begin
    emit_addi ctx "sp" "sp" (- ctx.frame_size);
    if not ctx.leaf then emit_sw ctx "ra" "sp" (ctx.frame_size - 4);
    List.iteri (fun i reg -> emit_sw ctx reg "sp" (saved_offset ctx i)) ctx.used_regs
  end

let emit_epilogue (ctx : emit_ctx) =
  if ctx.frame_size > 0 then begin
    List.iteri (fun i reg -> emit_lw ctx reg "sp" (saved_offset ctx i)) ctx.used_regs;
    if not ctx.leaf then emit_lw ctx "ra" "sp" (ctx.frame_size - 4);
    emit_addi ctx "sp" "sp" ctx.frame_size
  end;
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

let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |]

(* Emit moves that logically happen at once. Now that values can live in
   the argument registers, a destination may still be another move's
   source, so the moves are ordered rather than emitted as written; a
   cycle among them is broken by parking one value in scratch. *)
let emit_parallel_moves ctx moves =
  let pending = ref (List.filter (fun (dst, src) -> dst <> src) moves) in
  let scratch = "t0" in
  let progressing = ref true in
  while !progressing && !pending <> [] do
    let ready =
      List.find_opt
        (fun (dst, _) -> not (List.exists (fun (_, src) -> src = dst) !pending))
        !pending
    in
    match ready with
    | Some (dst, src) ->
      buf_emit ctx "  mv %s, %s\n" dst src;
      pending := List.filter (fun (d, _) -> d <> dst) !pending
    | None ->
      (* every destination is still someone's source: park one value so
         its register becomes free to overwrite *)
      (match !pending with
       | (dst, _) :: _ ->
         buf_emit ctx "  mv %s, %s\n" scratch dst;
         pending :=
           List.map
             (fun (d, s) -> if s = dst then (d, scratch) else (d, s))
             !pending
       | [] -> progressing := false)
  done

let emit_call ctx dst_opt name args =
  (* The outgoing area was reserved in the prologue, so sp stays put and
     spill slots keep their offsets while arguments are set up. *)
  let reg_moves = ref [] and from_spill = ref [] and onto_stack = ref [] in
  List.iteri (fun i t ->
    if i >= 8 then onto_stack := (i, t) :: !onto_stack
    else
      match Hashtbl.find ctx.temp_loc t with
      | Reg r -> reg_moves := (arg_regs.(i), r) :: !reg_moves
      | Spill slot -> from_spill := (arg_regs.(i), slot) :: !from_spill
  ) args;
  (* Stack arguments read their sources first, while no argument register
     has been overwritten yet. *)
  List.iter (fun (i, t) ->
    load_temp ctx "t0" t;
    emit_sw ctx "t0" "sp" ((i - 8) * 4)
  ) (List.rev !onto_stack);
  emit_parallel_moves ctx (List.rev !reg_moves);
  (* Reloads only write argument registers, so they cannot disturb moves
     that have already been emitted. *)
  List.iter (fun (r, slot) ->
    emit_lw ctx r "sp" (spill_offset ctx slot)
  ) (List.rev !from_spill);
  buf_emit ctx "  call %s\n" name;
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

(* dst = src * 2^k, emitted as the shift *)
let emit_shift_temp ctx dst src n =
  let s = src_reg ctx src "t0" in
  let d, finish = dst_reg ctx dst "t2" in
  (match shift_for_multiply n with
   | Some k -> buf_emit ctx "  slli %s, %s, %d\n" d s k
   | None -> invalid_arg "emit_shift_temp: factor is not a power of two");
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
  | IBinOp (dst, Mul, a, b) when Hashtbl.mem ctx.imm_temps b ->
    emit_shift_temp ctx dst a (Hashtbl.find ctx.imm_temps b)
  | IBinOp (dst, Mul, a, b) when Hashtbl.mem ctx.imm_temps a ->
    emit_shift_temp ctx dst b (Hashtbl.find ctx.imm_temps a)
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
  let frame = compute_frame func in
  let body = Array.of_list func.body in
  let offsets = instr_offsets (List.length frame.saved) body in
  let label_off = label_offsets offsets body in
  let ctx =
    { ctx with
      func;
      frame_size = frame.size;
      temp_loc = frame.locs;
      used_regs = frame.saved;
      imm_temps = frame.immediates;
      spill_base = frame.spill_base;
      leaf = frame.leaf;
      label_off;
      cur_off = 0 }
  in
  buf_emit ctx "\n  .text\n";
  buf_emit ctx "  .globl %s\n" func.name;
  buf_emit ctx "%s:\n" func.name;
  emit_prologue ctx;
  (* Entry copies from the argument registers to wherever each parameter
     was allocated. An unused parameter has no home and needs no copy;
     a parameter allocated to the register it arrived in needs none
     either, which is what the allocator's preference aims for. *)
  let entry_moves = ref [] and entry_spills = ref [] and from_stack = ref [] in
  List.iteri (fun i _p ->
    if Hashtbl.mem ctx.temp_loc i then begin
      if i >= 8 then from_stack := i :: !from_stack
      else
        match Hashtbl.find ctx.temp_loc i with
        | Reg r -> entry_moves := (r, arg_regs.(i)) :: !entry_moves
        | Spill slot -> entry_spills := (slot, arg_regs.(i)) :: !entry_spills
    end
  ) func.params;
  (* Stores read argument registers, so they run before any move can
     overwrite one. *)
  List.iter (fun (slot, r) ->
    emit_sw ctx r "sp" (spill_offset ctx slot)
  ) (List.rev !entry_spills);
  emit_parallel_moves ctx (List.rev !entry_moves);
  List.iter (fun i ->
    (* incoming stack arguments sit just above this frame *)
    emit_lw ctx "t0" "sp" (ctx.frame_size + ((i - 8) * 4));
    store_temp ctx "t0" i
  ) (List.rev !from_stack);
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
    spill_base = 0;
    leaf = true;
  } in
  emit_globals ctx prog.globals;
  List.iter (emit_func ctx) prog.funcs;
  Buffer.output_buffer out ctx.out
