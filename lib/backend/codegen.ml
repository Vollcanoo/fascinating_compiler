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
 *   Linear scan over conservative live intervals. Values are kept in
 *   callee-saved registers s1-s11 across calls; only excess values spill.
 *   Spill slots use s0-relative addressing so call-time sp adjustments do
 *   not invalidate their addresses.
 *)

open Ir
open Ast

type emit_ctx = {
  out : Buffer.t;
  func : func_ir;
  mutable frame_size : int;
  temp_loc : (int, temp_loc) Hashtbl.t;
  used_regs : string list;
  branch_cnt : int ref;
}

and temp_loc = Reg of string | Spill of int

let buf_emit ctx fmt = Printf.bprintf ctx.out fmt

let align16 n = (n + 15) land (lnot 15)

let instr_temps = function
  | ILoad (d, Imm _) | ILoad (d, Name _) | ILoadGlobal (d, _) -> [d]
  | ILoad (d, Temp s) | IUnaryOp (d, _, s) -> [d; s]
  | IStoreGlobal (_, s) | IBranchTrue (s, _) | IBranchFalse (s, _) -> [s]
  | IBinOp (d, _, l, r) -> [d; l; r]
  | ICall (d, _, args) -> d :: args
  | ICallVoid (_, args) -> args
  | IReturn (Some s) -> [s]
  | ILabel _ | IJump _ | IReturn None | IComment _ -> []

let allocate_registers func =
  let first = Array.make func.temp_count max_int in
  let last = Array.make func.temp_count min_int in
  List.iteri (fun i _ ->
    if i < func.temp_count then begin first.(i) <- -1; last.(i) <- -1 end
  ) func.params;
  List.iteri (fun pos ins ->
    List.iter (fun t ->
      if t >= 0 && t < func.temp_count then begin
        first.(t) <- min first.(t) pos;
        last.(t) <- max last.(t) pos
      end
    ) (instr_temps ins)
  ) func.body;
  let intervals = ref [] in
  for t = 0 to func.temp_count - 1 do
    if first.(t) <> max_int then intervals := (first.(t), last.(t), t) :: !intervals
  done;
  let intervals = List.sort compare !intervals in
  let free = ref ["s1"; "s2"; "s3"; "s4"; "s5"; "s6";
                  "s7"; "s8"; "s9"; "s10"; "s11"] in
  let active = ref [] in
  let locations = Hashtbl.create func.temp_count in
  let spill_count = ref 0 in
  let used = ref [] in
  List.iter (fun (start_pos, end_pos, temp) ->
    let still_active = ref [] in
    List.iter (fun (finish, reg) ->
      if finish < start_pos then free := reg :: !free
      else still_active := (finish, reg) :: !still_active
    ) !active;
    active := !still_active;
    match !free with
    | reg :: rest ->
      free := rest;
      Hashtbl.add locations temp (Reg reg);
      if not (List.mem reg !used) then used := reg :: !used;
      active := (end_pos, reg) :: !active
    | [] ->
      Hashtbl.add locations temp (Spill !spill_count);
      incr spill_count
  ) intervals;
  (locations, List.rev !used, !spill_count)

let compute_frame func =
  let temp_loc, used_regs, spill_count = allocate_registers func in
  let saved_slots = 2 + List.length used_regs in
  let frame_size = align16 ((saved_slots + spill_count) * 4) in
  (frame_size, temp_loc, used_regs)

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

let load_imm ctx reg n =
  buf_emit ctx "  li %s, %d\n" reg n

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
  load_temp ctx "t0" lhs;
  load_temp ctx "t1" rhs;
  (match op with
   | Add -> buf_emit ctx "  add t2, t0, t1\n"
   | Sub -> buf_emit ctx "  sub t2, t0, t1\n"
   | Mul -> buf_emit ctx "  mul t2, t0, t1\n"
   | Div -> buf_emit ctx "  div t2, t0, t1\n"
   | Mod -> buf_emit ctx "  rem t2, t0, t1\n"
   | Lt ->  buf_emit ctx "  slt t2, t0, t1\n"
   | Gt ->  buf_emit ctx "  slt t2, t1, t0\n"
   | Le ->
     buf_emit ctx "  slt t2, t1, t0\n";
     buf_emit ctx "  xori t2, t2, 1\n"
   | Ge ->
     buf_emit ctx "  slt t2, t0, t1\n";
     buf_emit ctx "  xori t2, t2, 1\n"
   | Eq ->
     buf_emit ctx "  sub t2, t0, t1\n";
     buf_emit ctx "  seqz t2, t2\n"
   | Ne ->
     buf_emit ctx "  sub t2, t0, t1\n";
     buf_emit ctx "  snez t2, t2\n"
   | And ->
     buf_emit ctx "  snez t0, t0\n";
     buf_emit ctx "  snez t1, t1\n";
     buf_emit ctx "  and t2, t0, t1\n"
   | Or ->
     buf_emit ctx "  or t2, t0, t1\n";
     buf_emit ctx "  snez t2, t2\n");
  store_temp ctx "t2" dst

let emit_unaryop ctx dst op src =
  load_temp ctx "t0" src;
  (match op with
   | UPlus -> buf_emit ctx "  mv t2, t0\n"
   | UMinus -> buf_emit ctx "  neg t2, t0\n"
   | Not ->  buf_emit ctx "  seqz t2, t0\n");
  store_temp ctx "t2" dst

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

let emit_instr ctx instr =
  match instr with
  | ILoad (dst, Imm n) ->
    load_imm ctx "t0" n;
    store_temp ctx "t0" dst
  | ILoad (dst, Temp src) ->
    load_temp ctx "t0" src;
    store_temp ctx "t0" dst
  | ILoad (dst, Name name) ->
    emit_global_addr ctx "t0" name;
    buf_emit ctx "  lw t0, 0(t0)\n";
    store_temp ctx "t0" dst
  | ILoadGlobal (dst, name) ->
    emit_global_addr ctx "t0" name;
    buf_emit ctx "  lw t0, 0(t0)\n";
    store_temp ctx "t0" dst
  | IStoreGlobal (name, src) ->
    load_temp ctx "t0" src;
    emit_global_addr ctx "t1" name;
    buf_emit ctx "  sw t0, 0(t1)\n"
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
  | IBranchTrue (t, lbl) ->
    load_temp ctx "t0" t;
    let n = !(ctx.branch_cnt) in
    ctx.branch_cnt := n + 1;
    let skip = Printf.sprintf ".Lskip%d" n in
    buf_emit ctx "  beqz t0, %s\n" skip;
    buf_emit ctx "  j %s\n" lbl;
    buf_emit ctx "%s:\n" skip
  | IBranchFalse (t, lbl) ->
    load_temp ctx "t0" t;
    let n = !(ctx.branch_cnt) in
    ctx.branch_cnt := n + 1;
    let skip = Printf.sprintf ".Lskip%d" n in
    buf_emit ctx "  bnez t0, %s\n" skip;
    buf_emit ctx "  j %s\n" lbl;
    buf_emit ctx "%s:\n" skip
  | IReturn opt ->
    (match opt with
     | Some t -> load_temp ctx "a0" t
     | None -> ());
    emit_epilogue ctx
  | IComment s ->
    buf_emit ctx "  # %s\n" s

let emit_func ctx func =
  let (frame_size, temp_loc, used_regs) = compute_frame func in
  let ctx = { ctx with func; frame_size; temp_loc; used_regs } in
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
  List.iter (emit_instr ctx) func.body

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
  } in
  emit_globals ctx prog.globals;
  List.iter (emit_func ctx) prog.funcs;
  Buffer.output_buffer out ctx.out
