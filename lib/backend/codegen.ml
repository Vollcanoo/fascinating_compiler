(** RISC-V32 code generation.

    Calling convention (standard RISC-V ILP32):
      a0-a7  argument registers, a0 also carries the return value
      ra     return address
      sp     stack pointer, 16-byte aligned
      s0/fp  frame base
      t0-t2  code generator scratch, t6 large-offset scratch
      t3-t5  allocatable caller-saved registers
      s1-s11 allocatable callee-saved registers

    Stack frame (only emitted when the function needs one):

      high address
      +---------------------+ <- s0 + frame_size = caller's sp
      | incoming stack args |  arguments 9 and up
      +---------------------+
      | saved ra            |  sp + frame_size - 4
      | saved s0            |  only when a frame pointer is needed
      | saved s1..s11       |  only the ones this function allocated
      | spill slots         |  slot k at s0 + 4k
      +---------------------+ <- sp (= s0 when there is a frame pointer)
      low address

    sp only ever moves inside a call sequence that passes arguments on the
    stack, and it is restored immediately afterwards, so everything except the
    spill area can be addressed from sp.  Spill slots cannot: an argument may be
    loaded out of one while sp is still displaced.  A frame pointer is therefore
    set up exactly when the function spills, and a leaf function that neither
    spills nor uses a callee-saved register gets no frame at all. *)

open Ir
open Ast

type ctx = {
  alloc : Regalloc.allocation;
  frame_size : int;
  use_frame : bool;
  use_frame_pointer : bool;
}

let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |]

let align16 n = (n + 15) land (lnot 15)

let fits12 = Target.fits12

let line fmt = Printf.ksprintf (fun s -> [s]) fmt

(* =====================================================
   Primitive emitters
   ===================================================== *)

let emit_mv dst src = if dst = src then [] else line "  mv %s, %s" dst src

let emit_li dst value = line "  li %s, %d" dst value

let emit_addi dst src imm =
  if imm = 0 then emit_mv dst src
  else if fits12 imm then line "  addi %s, %s, %d" dst src imm
  else emit_li "t6" imm @ line "  add %s, %s, t6" dst src

let emit_lw dst base offset =
  if fits12 offset then line "  lw %s, %d(%s)" dst offset base
  else
    emit_li "t6" offset
    @ line "  add t6, %s, t6" base
    @ line "  lw %s, 0(t6)" dst

let emit_sw src base offset =
  if fits12 offset then line "  sw %s, %d(%s)" src offset base
  else
    emit_li "t6" offset
    @ line "  add t6, %s, t6" base
    @ line "  sw %s, 0(t6)" src

let spill_offset slot = slot * 4

(* Loads an operand into [target], which is always a physical register. *)
let load_into ctx target = function
  | Imm value -> emit_li target value
  | Temp t ->
    (match Regalloc.location ctx.alloc t with
     | Regalloc.Reg phys -> emit_mv target phys
     | Regalloc.Spill slot -> emit_lw target "s0" (spill_offset slot))

(* Returns the register holding [operand], materialising it in [fallback] only
   when it is not already sitting in one.  Zero is free: x0 always reads 0. *)
let operand_reg ctx fallback = function
  | Imm 0 -> ([], "zero")
  | Imm value -> (emit_li fallback value, fallback)
  | Temp t ->
    (match Regalloc.location ctx.alloc t with
     | Regalloc.Reg phys -> ([], phys)
     | Regalloc.Spill slot -> (emit_lw fallback "s0" (spill_offset slot), fallback))

(* Where a result should be computed: straight into its home register when it
   has one, otherwise into scratch on the way to its spill slot. *)
let result_reg ctx dst fallback =
  match Regalloc.location ctx.alloc dst with
  | Regalloc.Reg phys -> phys
  | Regalloc.Spill _ -> fallback

let store_result ctx reg dst =
  match Regalloc.location ctx.alloc dst with
  | Regalloc.Reg phys -> emit_mv phys reg
  | Regalloc.Spill slot -> emit_sw reg "s0" (spill_offset slot)

(* =====================================================
   Strength reduction
   ===================================================== *)

let is_power_of_two = Target.is_power_of_two
let log2 = Target.log2

let emit_slli dst src amount =
  if amount = 0 then emit_mv dst src else line "  slli %s, %s, %d" dst src amount

(* Multiplication by a constant, expressed with shifts and one add/sub.  t1 and
   t2 are free here: the immediate operand means no second load used them. *)
let rec emit_mul_plan target source (plan : Target.mul_plan) =
  match plan with
  | Target.MulZero -> emit_li target 0
  | Target.MulIdentity -> emit_mv target source
  | Target.MulNegated Target.MulIdentity -> line "  neg %s, %s" target source
  | Target.MulShift amount -> emit_slli target source amount
  | Target.MulShiftAdd amount ->
    emit_slli "t1" source amount @ line "  add %s, t1, %s" target source
  | Target.MulShiftSub amount ->
    emit_slli "t1" source amount @ line "  sub %s, t1, %s" target source
  | Target.MulTwoShifts (first, second) ->
    emit_slli "t1" source first
    @ emit_slli "t2" source second
    @ line "  add %s, t1, t2" target
  | Target.MulNegated inner ->
    emit_mul_plan target source inner @ line "  neg %s, %s" target target

(* Signed division by 2^k rounds towards zero, so a negative dividend needs the
   2^k-1 bias added before the arithmetic shift. *)
let div_by_pow2 target source amount =
  if amount = 0 then emit_mv target source
  else
    line "  srai t1, %s, 31" source
    @ line "  srli t1, t1, %d" (32 - amount)
    @ line "  add t1, %s, t1" source
    @ line "  srai %s, t1, %d" target amount

let mod_by_pow2 target source amount =
  if amount = 0 then emit_li target 0
  else
    line "  srai t1, %s, 31" source
    @ line "  srli t1, t1, %d" (32 - amount)
    @ line "  add t1, %s, t1" source
    @ line "  srai t1, t1, %d" amount
    @ line "  slli t1, t1, %d" amount
    @ line "  sub %s, %s, t1" target source

(* =====================================================
   Binary operations
   ===================================================== *)

let emit_binop ctx dst op lhs rhs =
  let target = result_reg ctx dst "t2" in
  let finish code = code @ store_result ctx target dst in
  let with_operand operand build =
    let load, reg = operand_reg ctx "t0" operand in
    finish (load @ build target reg)
  in
  let generic () =
    let lhs_load, lhs_reg = operand_reg ctx "t0" lhs in
    let rhs_load, rhs_reg = operand_reg ctx "t1" rhs in
    let code =
      match op with
      | Add -> line "  add %s, %s, %s" target lhs_reg rhs_reg
      | Sub -> line "  sub %s, %s, %s" target lhs_reg rhs_reg
      | Mul -> line "  mul %s, %s, %s" target lhs_reg rhs_reg
      | Div -> line "  div %s, %s, %s" target lhs_reg rhs_reg
      | Mod -> line "  rem %s, %s, %s" target lhs_reg rhs_reg
      | Lt -> line "  slt %s, %s, %s" target lhs_reg rhs_reg
      | Gt -> line "  slt %s, %s, %s" target rhs_reg lhs_reg
      | Le ->
        line "  slt %s, %s, %s" target rhs_reg lhs_reg
        @ line "  xori %s, %s, 1" target target
      | Ge ->
        line "  slt %s, %s, %s" target lhs_reg rhs_reg
        @ line "  xori %s, %s, 1" target target
      | Eq ->
        line "  sub %s, %s, %s" target lhs_reg rhs_reg
        @ line "  seqz %s, %s" target target
      | Ne ->
        line "  sub %s, %s, %s" target lhs_reg rhs_reg
        @ line "  snez %s, %s" target target
      | And ->
        line "  snez t0, %s" lhs_reg
        @ line "  snez t1, %s" rhs_reg
        @ line "  and %s, t0, t1" target
      | Or ->
        line "  or %s, %s, %s" target lhs_reg rhs_reg
        @ line "  snez %s, %s" target target
    in
    finish (lhs_load @ rhs_load @ code)
  in
  match op, lhs, rhs with
  | Add, operand, Imm imm | Add, Imm imm, operand ->
    with_operand operand (fun target reg -> emit_addi target reg imm)
  | Sub, operand, Imm imm when imm <> min_i32 ->
    with_operand operand (fun target reg -> emit_addi target reg (-imm))
  | Sub, Imm 0, operand ->
    with_operand operand (fun target reg -> line "  neg %s, %s" target reg)
  | (Eq | Ne), operand, Imm 0 | (Eq | Ne), Imm 0, operand ->
    let mnemonic = match op with Eq -> "seqz" | _ -> "snez" in
    with_operand operand (fun target reg -> line "  %s %s, %s" mnemonic target reg)
  | Lt, operand, Imm imm when fits12 imm ->
    with_operand operand (fun target reg -> line "  slti %s, %s, %d" target reg imm)
  | Ge, operand, Imm imm when fits12 imm ->
    with_operand operand (fun target reg ->
      line "  slti %s, %s, %d" target reg imm @ line "  xori %s, %s, 1" target target)
  | Le, operand, Imm imm when imm <> max_i32 && fits12 (imm + 1) ->
    with_operand operand (fun target reg ->
      line "  slti %s, %s, %d" target reg (imm + 1))
  | Gt, operand, Imm imm when imm <> max_i32 && fits12 (imm + 1) ->
    with_operand operand (fun target reg ->
      line "  slti %s, %s, %d" target reg (imm + 1)
      @ line "  xori %s, %s, 1" target target)
  | Mul, operand, Imm imm | Mul, Imm imm, operand ->
    (match Target.mul_plan imm with
     | Some plan ->
       let load, reg = operand_reg ctx "t0" operand in
       finish (load @ emit_mul_plan target reg plan)
     | None -> generic ())
  | Div, operand, Imm imm when is_power_of_two imm ->
    let load, reg = operand_reg ctx "t0" operand in
    finish (load @ div_by_pow2 target reg (log2 imm))
  | Div, operand, Imm imm when imm <> min_i32 && imm < 0 && is_power_of_two (-imm) ->
    let load, reg = operand_reg ctx "t0" operand in
    finish (load @ div_by_pow2 target reg (log2 (-imm)) @ line "  neg %s, %s" target target)
  | Mod, operand, Imm imm when is_power_of_two imm ->
    let load, reg = operand_reg ctx "t0" operand in
    finish (load @ mod_by_pow2 target reg (log2 imm))
  | Mod, operand, Imm imm when imm <> min_i32 && imm < 0 && is_power_of_two (-imm) ->
    let load, reg = operand_reg ctx "t0" operand in
    finish (load @ mod_by_pow2 target reg (log2 (-imm)))
  | _ -> generic ()

let emit_unaryop ctx dst op operand =
  let target = result_reg ctx dst "t2" in
  let load, reg = operand_reg ctx "t0" operand in
  let code =
    match op with
    | UPlus -> emit_mv target reg
    | UMinus -> line "  neg %s, %s" target reg
    | Not -> line "  seqz %s, %s" target reg
  in
  load @ code @ store_result ctx target dst

let emit_shift_left ctx dst operand amount =
  let target = result_reg ctx dst "t2" in
  let load, reg = operand_reg ctx "t0" operand in
  load @ emit_slli target reg amount @ store_result ctx target dst

(* =====================================================
   Branches

   A comparison feeding a branch never has to be materialised as a 0/1 value:
   the RISC-V conditional branches compare two registers directly.
   ===================================================== *)

let inverse_comparison = function
  | Lt -> Some Ge
  | Ge -> Some Lt
  | Gt -> Some Le
  | Le -> Some Gt
  | Eq -> Some Ne
  | Ne -> Some Eq
  | Add | Sub | Mul | Div | Mod | And | Or -> None

let emit_branch_compare ctx op lhs rhs label =
  let lhs_load, lhs_reg = operand_reg ctx "t0" lhs in
  let rhs_load, rhs_reg = operand_reg ctx "t1" rhs in
  let branch =
    match op with
    | Lt -> line "  blt %s, %s, %s" lhs_reg rhs_reg label
    | Gt -> line "  blt %s, %s, %s" rhs_reg lhs_reg label
    | Le -> line "  bge %s, %s, %s" rhs_reg lhs_reg label
    | Ge -> line "  bge %s, %s, %s" lhs_reg rhs_reg label
    | Eq -> line "  beq %s, %s, %s" lhs_reg rhs_reg label
    | Ne -> line "  bne %s, %s, %s" lhs_reg rhs_reg label
    | Add | Sub | Mul | Div | Mod | And | Or -> []
  in
  lhs_load @ rhs_load @ branch

let emit_branch ctx operand label ~when_zero =
  match operand with
  | Imm 0 -> if when_zero then line "  j %s" label else []
  | Imm _ -> if when_zero then [] else line "  j %s" label
  | Temp _ ->
    let load, reg = operand_reg ctx "t0" operand in
    load @ line "  %s %s, %s" (if when_zero then "beqz" else "bnez") reg label

(* =====================================================
   Calls, prologue and epilogue
   ===================================================== *)

let incoming_arg_offset ctx index = ctx.frame_size + ((index - 8) * 4)

let emit_call ctx dst name args =
  let stack_args = max 0 (List.length args - 8) in
  let stack_bytes = align16 (stack_args * 4) in
  let setup = if stack_bytes = 0 then [] else emit_addi "sp" "sp" (-stack_bytes) in
  let pass =
    List.concat
      (List.mapi (fun index operand ->
        if index < 8 then load_into ctx arg_regs.(index) operand
        else load_into ctx "t0" operand @ emit_sw "t0" "sp" ((index - 8) * 4)
      ) args)
  in
  let cleanup = if stack_bytes = 0 then [] else emit_addi "sp" "sp" stack_bytes in
  let save = match dst with None -> [] | Some dst -> store_result ctx "a0" dst in
  setup @ pass @ line "  call %s" name @ cleanup @ save

let ra_offset ctx = ctx.frame_size - 4

let s0_offset ctx = ctx.frame_size - 8

let saved_reg_offset ctx index =
  ctx.frame_size - 4 - (if ctx.use_frame_pointer then 4 else 0) - 4 - (index * 4)

let emit_prologue ctx =
  if not ctx.use_frame then []
  else
    emit_addi "sp" "sp" (-ctx.frame_size)
    @ emit_sw "ra" "sp" (ra_offset ctx)
    @ (if ctx.use_frame_pointer then emit_sw "s0" "sp" (s0_offset ctx) else [])
    @ List.concat
        (List.mapi (fun index reg -> emit_sw reg "sp" (saved_reg_offset ctx index))
           ctx.alloc.Regalloc.used_regs)
    @ (if ctx.use_frame_pointer then emit_mv "s0" "sp" else [])

let emit_epilogue ctx =
  if not ctx.use_frame then line "  ret"
  else
    List.concat
      (List.mapi (fun index reg -> emit_lw reg "sp" (saved_reg_offset ctx index))
         ctx.alloc.Regalloc.used_regs)
    @ emit_lw "ra" "sp" (ra_offset ctx)
    @ (if ctx.use_frame_pointer then emit_lw "s0" "sp" (s0_offset ctx) else [])
    @ emit_addi "sp" "sp" ctx.frame_size
    @ line "  ret"

(* =====================================================
   Instruction dispatch
   ===================================================== *)

let emit_instr ctx = function
  | ILoadParam (dst, index) ->
    if index < 8 then store_result ctx arg_regs.(index) dst
    else
      let target = result_reg ctx dst "t0" in
      emit_lw target "sp" (incoming_arg_offset ctx index)
      @ store_result ctx target dst
  | ILoad (dst, operand) ->
    (match Regalloc.location ctx.alloc dst with
     | Regalloc.Reg phys -> load_into ctx phys operand
     | Regalloc.Spill _ -> load_into ctx "t0" operand @ store_result ctx "t0" dst)
  | ILoadGlobal (dst, name) ->
    let target = result_reg ctx dst "t1" in
    line "  la t0, %s" name
    @ line "  lw %s, 0(t0)" target
    @ store_result ctx target dst
  | IStoreGlobal (name, operand) ->
    let load, reg = operand_reg ctx "t0" operand in
    load @ line "  la t1, %s" name @ line "  sw %s, 0(t1)" reg
  | IUnaryOp (dst, op, operand) -> emit_unaryop ctx dst op operand
  | IBinOp (dst, op, lhs, rhs) -> emit_binop ctx dst op lhs rhs
  | IShiftLeft (dst, operand, amount) -> emit_shift_left ctx dst operand amount
  | ICall (dst, name, args) -> emit_call ctx dst name args
  | ILabel label -> line "%s:" label
  | IJump label -> line "  j %s" label
  | IBranchZero (operand, label) -> emit_branch ctx operand label ~when_zero:true
  | IBranchNonZero (operand, label) -> emit_branch ctx operand label ~when_zero:false
  | IReturn operand ->
    let load = match operand with None -> [] | Some o -> load_into ctx "a0" o in
    load @ emit_epilogue ctx

let is_comparison = function Lt | Gt | Le | Ge | Eq | Ne -> true | _ -> false

let rec temp_used_later t = function
  | [] -> false
  | instr :: rest ->
    if List.exists (fun o -> o = Temp t) (instr_operands instr) then true
    else if instr_dest instr = Some t then false
    else temp_used_later t rest

(* IR-level peephole: fuse a comparison into the branch that consumes it, and
   let a call whose result is returned unchanged leave its value in a0. *)
let emit_body ctx body =
  let rec loop acc = function
    | IBinOp (dst, op, lhs, rhs) :: IBranchZero (Temp t, label) :: rest
      when dst = t && is_comparison op && not (temp_used_later t rest) ->
      let inverse = Option.get (inverse_comparison op) in
      loop (List.rev_append (emit_branch_compare ctx inverse lhs rhs label) acc) rest
    | IBinOp (dst, op, lhs, rhs) :: IBranchNonZero (Temp t, label) :: rest
      when dst = t && is_comparison op && not (temp_used_later t rest) ->
      loop (List.rev_append (emit_branch_compare ctx op lhs rhs label) acc) rest
    | ICall (Some dst, name, args) :: IReturn (Some (Temp result)) :: rest
      when dst = result && not (temp_used_later dst rest) ->
      loop
        (List.rev_append (emit_call ctx None name args @ emit_epilogue ctx) acc)
        rest
    | instr :: rest -> loop (List.rev_append (emit_instr ctx instr) acc) rest
    | [] -> List.rev acc
  in
  loop [] body

(* =====================================================
   Assembly-level peephole
   ===================================================== *)

let parse_two_operand opcode text =
  let prefix = "  " ^ opcode ^ " " in
  let plen = String.length prefix in
  if String.length text <= plen || String.sub text 0 plen <> prefix then None
  else
    let rest = String.sub text plen (String.length text - plen) in
    match String.index_opt rest ',' with
    | None -> None
    | Some index ->
      Some
        (String.trim (String.sub rest 0 index),
         String.trim (String.sub rest (index + 1) (String.length rest - index - 1)))

let peephole lines =
  let rec loop acc = function
    | first :: second :: rest ->
      (match parse_two_operand "mv" first, parse_two_operand "mv" second with
       (* mv a, b followed by mv b, a: the second move is a no-op *)
       | Some (dst, src), Some (dst2, src2) when dst = src2 && src = dst2 ->
         loop (first :: acc) rest
       | _ ->
         (match parse_two_operand "sw" first, parse_two_operand "lw" second with
          (* storing then reloading the same slot: reuse the value in registers *)
          | Some (src, store_mem), Some (dst, load_mem) when store_mem = load_mem ->
            loop (List.rev_append (emit_mv dst src) (first :: acc)) rest
          | _ ->
            (match parse_two_operand "lw" first, parse_two_operand "sw" second with
             (* loading a slot then storing it straight back changes nothing *)
             | Some (dst, load_mem), Some (src, store_mem)
               when dst = src && load_mem = store_mem -> loop (first :: acc) rest
             | _ -> loop (first :: acc) (second :: rest))))
    | instr :: rest -> loop (instr :: acc) rest
    | [] -> List.rev acc
  in
  loop [] lines

(* =====================================================
   Program
   ===================================================== *)

let max_param_index body =
  List.fold_left (fun current -> function
    | ILoadParam (_, index) -> max current index
    | _ -> current
  ) (-1) body

let emit_func (func : func_ir) =
  let alloc = Regalloc.allocate func in
  let uses_call = List.exists (function ICall _ -> true | _ -> false) func.body in
  let use_frame =
    uses_call || alloc.Regalloc.spill_slots > 0 || alloc.Regalloc.used_regs <> []
  in
  (* s0 is only needed to reach spill slots while sp is displaced by an
     outgoing stack argument. *)
  let use_frame_pointer = alloc.Regalloc.spill_slots > 0 in
  let frame_size =
    if not use_frame then 0
    else
      align16
        (4
         + (if use_frame_pointer then 4 else 0)
         + (4 * List.length alloc.Regalloc.used_regs)
         + (4 * alloc.Regalloc.spill_slots))
  in
  let ctx = { alloc; frame_size; use_frame; use_frame_pointer } in
  line "  .text"
  @ line "  .globl %s" func.name
  @ line "%s:" func.name
  @ peephole (emit_prologue ctx @ emit_body ctx func.body)

let emit_globals globals =
  if globals = [] then []
  else
    line "  .data"
    @ List.concat_map (fun g ->
      let name, value =
        match g with GConst (name, value) | GVar (name, value) -> (name, value)
      in
      line "  .globl %s" name
      @ line "  .align 2"
      @ line "%s:" name
      @ line "  .word %d" value
    ) globals

let emit (out : out_channel) (prog : program) : unit =
  let lines =
    emit_globals prog.globals @ List.concat_map emit_func prog.funcs
  in
  List.iter (fun l -> output_string out l; output_char out '\n') lines

(* Exposed for the tests. *)
let assembly (prog : program) =
  let buffer = Buffer.create 4096 in
  List.iter (fun l -> Buffer.add_string buffer l; Buffer.add_char buffer '\n')
    (emit_globals prog.globals @ List.concat_map emit_func prog.funcs);
  Buffer.contents buffer
