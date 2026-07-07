(** Intermediate representation for ToyC — three-address code style *)

open Ast

type operand =
  | Imm of int
  | Temp of int
  | Name of string  (* global variable / function name *)

type label = string

type instr =
  | ILoad of int * operand         (* dst_temp <- operand (move/load) *)
  | ILoadGlobal of int * string    (* dst_temp <- global variable *)
  | IStoreGlobal of string * int   (* global variable <- src_temp *)
  | IBinOp of int * bin_op * int * int   (* dst <- op lhs rhs *)
  | IUnaryOp of int * unary_op * int     (* dst <- op src *)
  | ICall of int * string * int list     (* dst <- call func args *)
  | ICallVoid of string * int list       (* call func args (no return) *)
  | ILabel of label
  | IJump of label
  | IBranchTrue of int * label     (* if temp != 0 goto label *)
  | IBranchFalse of int * label    (* if temp == 0 goto label *)
  | IReturn of int option          (* return [temp] *)
  | IComment of string

type func_ir = {
  name : string;
  ret_type : func_ret_type;
  params : string list;
  locals : string list;
  body : instr list;
  temp_count : int;
}

type global =
  | GConst of string * int
  | GVar of string * int   (* name, initial value *)

type program = {
  globals : global list;
  funcs : func_ir list;
}

(* --- IR generation from AST --- *)

type gen_env = {
  mutable next_temp : int;
  mutable next_label : int;
  mutable instrs : instr list;
  mutable locals : string list;
  vars : (string, [`Temp of int | `Global of string | `Const of int]) Hashtbl.t;
  loop_stack : (label * label) Stack.t;  (* (continue_label, break_label) *)
}

let new_env () = {
  next_temp = 0;
  next_label = 0;
  instrs = [];
  locals = [];
  vars = Hashtbl.create 32;
  loop_stack = Stack.create ();
}

let fresh_temp env =
  let t = env.next_temp in
  env.next_temp <- env.next_temp + 1;
  t

let fresh_label env prefix =
  let n = env.next_label in
  env.next_label <- env.next_label + 1;
  Printf.sprintf ".L%s%d" prefix n

let emit env instr = env.instrs <- instr :: env.instrs

let rec gen_expr env (e : exp) : int =
  match e with
  | IntLit n ->
    let t = fresh_temp env in
    emit env (ILoad (t, Imm n));
    t
  | Var name ->
    (match Hashtbl.find_opt env.vars name with
     | Some (`Temp t) -> t
     | Some (`Global g) ->
       let t = fresh_temp env in
       emit env (ILoadGlobal (t, g));
       t
     | Some (`Const n) ->
       let t = fresh_temp env in
       emit env (ILoad (t, Imm n));
       t
     | None ->
       let t = fresh_temp env in
       emit env (ILoadGlobal (t, name));
       t)
  | Unary (op, sub) ->
    (match op with
     | Not -> gen_not env sub
     | _ ->
       let s = gen_expr env sub in
       let t = fresh_temp env in
       emit env (IUnaryOp (t, op, s));
       t)
  | Binary (lhs, And, rhs) -> gen_short_circuit_and env lhs rhs
  | Binary (lhs, Or, rhs) -> gen_short_circuit_or env lhs rhs
  | Binary (lhs, op, rhs) ->
    let l = gen_expr env lhs in
    let r = gen_expr env rhs in
    let t = fresh_temp env in
    emit env (IBinOp (t, op, l, r));
    t
  | Call (name, args) ->
    let arg_temps = List.map (gen_expr env) args in
    let t = fresh_temp env in
    emit env (ICall (t, name, arg_temps));
    t

and gen_not env sub =
  let s = gen_expr env sub in
  let t = fresh_temp env in
  emit env (IUnaryOp (t, Not, s));
  t

and gen_short_circuit_and env lhs rhs =
  let result = fresh_temp env in
  let l_false = fresh_label env "and_false" in
  let l_end = fresh_label env "and_end" in
  let l = gen_expr env lhs in
  emit env (IBranchFalse (l, l_false));
  let r = gen_expr env rhs in
  emit env (IBranchFalse (r, l_false));
  emit env (ILoad (result, Imm 1));
  emit env (IJump l_end);
  emit env (ILabel l_false);
  emit env (ILoad (result, Imm 0));
  emit env (ILabel l_end);
  result

and gen_short_circuit_or env lhs rhs =
  let result = fresh_temp env in
  let l_true = fresh_label env "or_true" in
  let l_end = fresh_label env "or_end" in
  let l = gen_expr env lhs in
  emit env (IBranchTrue (l, l_true));
  let r = gen_expr env rhs in
  emit env (IBranchTrue (r, l_true));
  emit env (ILoad (result, Imm 0));
  emit env (IJump l_end);
  emit env (ILabel l_true);
  emit env (ILoad (result, Imm 1));
  emit env (ILabel l_end);
  result

let gen_store_var env name src_temp =
  match Hashtbl.find_opt env.vars name with
  | Some (`Temp dst) ->
    if dst <> src_temp then
      emit env (ILoad (dst, Temp src_temp))
  | Some (`Global g) ->
    emit env (IStoreGlobal (g, src_temp))
  | _ ->
    emit env (IStoreGlobal (name, src_temp))

let rec gen_stmt env (s : stmt) : unit =
  match s with
  | Empty -> ()
  | ExprStmt e ->
    ignore (gen_expr env e)
  | Assign (name, e) ->
    let t = gen_expr env e in
    gen_store_var env name t
  | ConstDecl (name, e) ->
    let dst = fresh_temp env in
    Hashtbl.replace env.vars name (`Temp dst);
    let t = gen_expr env e in
    if t <> dst then emit env (ILoad (dst, Temp t))
  | VarDecl (name, e) ->
    env.locals <- name :: env.locals;
    let dst = fresh_temp env in
    Hashtbl.replace env.vars name (`Temp dst);
    let t = gen_expr env e in
    if t <> dst then emit env (ILoad (dst, Temp t))
  | Block body ->
    List.iter (gen_stmt env) body
  | If (cond, then_s, else_s) ->
    gen_if env cond then_s else_s
  | While (cond, body) ->
    gen_while env cond body
  | Break ->
    let (_, break_lbl) = Stack.top env.loop_stack in
    emit env (IJump break_lbl)
  | Continue ->
    let (cont_lbl, _) = Stack.top env.loop_stack in
    emit env (IJump cont_lbl)
  | Return None ->
    emit env (IReturn None)
  | Return (Some e) ->
    let t = gen_expr env e in
    emit env (IReturn (Some t))

and gen_if env cond then_s else_s =
  match else_s with
  | None ->
    let l_end = fresh_label env "if_end" in
    let c = gen_expr env cond in
    emit env (IBranchFalse (c, l_end));
    gen_stmt env then_s;
    emit env (ILabel l_end)
  | Some else_stmt ->
    let l_else = fresh_label env "else" in
    let l_end = fresh_label env "if_end" in
    let c = gen_expr env cond in
    emit env (IBranchFalse (c, l_else));
    gen_stmt env then_s;
    emit env (IJump l_end);
    emit env (ILabel l_else);
    gen_stmt env else_stmt;
    emit env (ILabel l_end)

and gen_while env cond body =
  let l_cond = fresh_label env "while_cond" in
  let l_end = fresh_label env "while_end" in
  Stack.push (l_cond, l_end) env.loop_stack;
  emit env (ILabel l_cond);
  let c = gen_expr env cond in
  emit env (IBranchFalse (c, l_end));
  gen_stmt env body;
  emit env (IJump l_cond);
  emit env (ILabel l_end);
  ignore (Stack.pop env.loop_stack)

let gen_func (globals : (string * [`Const of int | `Var]) list) (fd : func_def) : func_ir =
  let env = new_env () in
  List.iter (fun (name, kind) ->
    match kind with
    | `Const n -> Hashtbl.replace env.vars name (`Const n)
    | `Var -> Hashtbl.replace env.vars name (`Global name)
  ) globals;
  List.iter (fun p ->
    let t = fresh_temp env in
    Hashtbl.replace env.vars p (`Temp t)
  ) fd.params;
  List.iter (gen_stmt env) fd.body;
  (match fd.ret_type with
   | VoidRet ->
     (match env.instrs with
      | IReturn _ :: _ -> ()
      | _ -> emit env (IReturn None))
   | IntRet -> ());
  {
    name = fd.name;
    ret_type = fd.ret_type;
    params = fd.params;
    locals = List.rev env.locals;
    body = List.rev env.instrs;
    temp_count = env.next_temp;
  }

let rec eval_const_init = function
  | IntLit n -> n
  | Unary (UMinus, e) -> -(eval_const_init e)
  | Unary (UPlus, e) -> eval_const_init e
  | Unary (Not, e) -> if eval_const_init e = 0 then 1 else 0
  | Binary (lhs, Add, rhs) -> eval_const_init lhs + eval_const_init rhs
  | Binary (lhs, Sub, rhs) -> eval_const_init lhs - eval_const_init rhs
  | Binary (lhs, Mul, rhs) -> eval_const_init lhs * eval_const_init rhs
  | Binary (lhs, Div, rhs) -> eval_const_init lhs / eval_const_init rhs
  | Binary (lhs, Mod, rhs) -> eval_const_init lhs mod eval_const_init rhs
  | _ -> 0

let lower (cu : comp_unit) : program =
  let globals = ref [] in
  let global_info = ref [] in
  let funcs = ref [] in
  List.iter (fun tl ->
    match tl with
    | GlobalConstDecl (name, e) ->
      let value = eval_const_init e in
      globals := GConst (name, value) :: !globals;
      global_info := (name, `Const value) :: !global_info
    | GlobalVarDecl (name, e) ->
      let value = eval_const_init e in
      globals := GVar (name, value) :: !globals;
      global_info := (name, `Var) :: !global_info
    | FuncDef fd ->
      funcs := gen_func !global_info fd :: !funcs
  ) cu;
  { globals = List.rev !globals; funcs = List.rev !funcs }
