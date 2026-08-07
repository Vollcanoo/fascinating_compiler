(** Intermediate representation for ToyC — three-address code over an unbounded
    supply of virtual registers.

    Operands carry immediates directly, so a folded constant never has to be
    materialised in a register before it can be used.  That is what lets the
    optimizer rewrite [t = a + 1] instead of [t1 = 1; t = a + t1], and what lets
    the backend pick [addi]/[slti]/[slli] instead of a [li] plus a register-register
    instruction. *)

open Ast

type operand =
  | Imm of int
  | Temp of int

type label = string

type instr =
  (* dst <- incoming argument #index *)
  | ILoadParam of int * int
  | ILoad of int * operand
  | ILoadGlobal of int * string
  | IStoreGlobal of string * operand
  | IUnaryOp of int * unary_op * operand
  | IBinOp of int * bin_op * operand * operand
  (* dst <- src << amount; produced by strength reduction *)
  | IShiftLeft of int * operand * int
  | ICall of int option * string * operand list
  | ILabel of label
  | IJump of label
  | IBranchZero of operand * label
  | IBranchNonZero of operand * label
  | IReturn of operand option

type func_ir = {
  name : string;
  ret_type : func_ret_type;
  params : string list;
  body : instr list;
  temp_count : int;
}

type global =
  | GConst of string * int
  | GVar of string * int

type program = {
  globals : global list;
  funcs : func_ir list;
}

(* =====================================================
   32-bit constant evaluation

   ToyC values are 32-bit.  Folding with OCaml's native 63-bit integers would
   disagree with the generated code as soon as an expression overflows, so every
   folded result is wrapped through Int32.
   ===================================================== *)

let min_i32 = Int32.to_int Int32.min_int
let max_i32 = Int32.to_int Int32.max_int

let i32 value = Int32.to_int (Int32.of_int value)

let apply_unary (op : unary_op) value =
  match op with
  | UPlus -> i32 value
  | UMinus -> Int32.(to_int (neg (of_int value)))
  | Not -> if i32 value = 0 then 1 else 0

let apply_binary (op : bin_op) lhs rhs =
  let a = i32 lhs and b = i32 rhs in
  match op with
  | Add -> Some Int32.(to_int (add (of_int a) (of_int b)))
  | Sub -> Some Int32.(to_int (sub (of_int a) (of_int b)))
  | Mul -> Some Int32.(to_int (mul (of_int a) (of_int b)))
  (* RISC-V div/rem never trap: INT_MIN / -1 wraps and INT_MIN %% -1 is 0. *)
  | Div ->
    if b = 0 then None
    else if a = min_i32 && b = -1 then Some min_i32
    else Some Int32.(to_int (div (of_int a) (of_int b)))
  | Mod ->
    if b = 0 then None
    else if a = min_i32 && b = -1 then Some 0
    else Some Int32.(to_int (rem (of_int a) (of_int b)))
  | Lt -> Some (if a < b then 1 else 0)
  | Gt -> Some (if a > b then 1 else 0)
  | Le -> Some (if a <= b then 1 else 0)
  | Ge -> Some (if a >= b then 1 else 0)
  | Eq -> Some (if a = b then 1 else 0)
  | Ne -> Some (if a <> b then 1 else 0)
  | And -> Some (if a <> 0 && b <> 0 then 1 else 0)
  | Or -> Some (if a <> 0 || b <> 0 then 1 else 0)

let apply_shift_left value amount =
  Int32.(to_int (shift_left (of_int value) amount))

(* =====================================================
   Instruction shape helpers, shared by the CFG, the optimizer and the backend
   ===================================================== *)

let instr_dest = function
  | ILoadParam (dst, _)
  | ILoad (dst, _)
  | ILoadGlobal (dst, _)
  | IUnaryOp (dst, _, _)
  | IBinOp (dst, _, _, _)
  | IShiftLeft (dst, _, _) -> Some dst
  | ICall (dst, _, _) -> dst
  | IStoreGlobal _ | ILabel _ | IJump _ | IBranchZero _ | IBranchNonZero _
  | IReturn _ -> None

let instr_operands = function
  | ILoad (_, operand)
  | IUnaryOp (_, _, operand)
  | IShiftLeft (_, operand, _)
  | IStoreGlobal (_, operand)
  | IBranchZero (operand, _)
  | IBranchNonZero (operand, _) -> [operand]
  | IBinOp (_, _, lhs, rhs) -> [lhs; rhs]
  | ICall (_, _, args) -> args
  | IReturn (Some operand) -> [operand]
  | ILoadParam _ | ILoadGlobal _ | ILabel _ | IJump _ | IReturn None -> []

let map_operands f = function
  | ILoad (dst, operand) -> ILoad (dst, f operand)
  | IUnaryOp (dst, op, operand) -> IUnaryOp (dst, op, f operand)
  | IShiftLeft (dst, operand, amount) -> IShiftLeft (dst, f operand, amount)
  | IStoreGlobal (name, operand) -> IStoreGlobal (name, f operand)
  | IBinOp (dst, op, lhs, rhs) -> IBinOp (dst, op, f lhs, f rhs)
  | IBranchZero (operand, label) -> IBranchZero (f operand, label)
  | IBranchNonZero (operand, label) -> IBranchNonZero (f operand, label)
  | ICall (dst, name, args) -> ICall (dst, name, List.map f args)
  | IReturn (Some operand) -> IReturn (Some (f operand))
  | (ILoadParam _ | ILoadGlobal _ | ILabel _ | IJump _ | IReturn None) as instr ->
    instr

let operand_temp = function
  | Imm _ -> None
  | Temp t -> Some t

let max_temp body =
  let of_operand current operand =
    match operand_temp operand with
    | Some t -> max current t
    | None -> current
  in
  List.fold_left (fun current instr ->
    let current =
      match instr_dest instr with
      | Some dst -> max current dst
      | None -> current
    in
    List.fold_left of_operand current (instr_operands instr)
  ) (-1) body

(* =====================================================
   Lowering: AST -> IR
   ===================================================== *)

type var_binding = [ `Temp of int | `Global of string | `Const of int ]

type gen_env = {
  mutable next_temp : int;
  mutable instrs : instr list;
  mutable scopes : (string * var_binding) list list;
  loop_stack : (label * label) Stack.t;
}

let global_label_counter = ref 0

let new_env () = {
  next_temp = 0;
  instrs = [];
  scopes = [[]];
  loop_stack = Stack.create ();
}

let fresh_temp env =
  let t = env.next_temp in
  env.next_temp <- env.next_temp + 1;
  t

let fresh_label prefix =
  let n = !global_label_counter in
  global_label_counter := n + 1;
  Printf.sprintf ".L%s%d" prefix n

let emit env instr = env.instrs <- instr :: env.instrs

let enter_scope env = env.scopes <- [] :: env.scopes

let leave_scope env =
  match env.scopes with
  | _ :: rest -> env.scopes <- rest
  | [] -> ()

let add_var env (name : string) (binding : var_binding) =
  match env.scopes with
  | scope :: rest -> env.scopes <- ((name, binding) :: scope) :: rest
  | [] -> env.scopes <- [[(name, binding)]]

let lookup_var env name =
  let rec find_in_scopes = function
    | [] -> None
    | scope :: rest ->
      (match List.assoc_opt name scope with
       | Some _ as found -> found
       | None -> find_in_scopes rest)
  in
  find_in_scopes env.scopes

let rec gen_expr env (e : exp) : operand =
  match e with
  | IntLit n -> Imm (i32 n)
  | Var name ->
    (match lookup_var env name with
     | Some (`Temp t) -> Temp t
     | Some (`Const n) -> Imm n
     | Some (`Global g) ->
       let t = fresh_temp env in
       emit env (ILoadGlobal (t, g));
       Temp t
     | None ->
       let t = fresh_temp env in
       emit env (ILoadGlobal (t, name));
       Temp t)
  | Unary (op, sub) ->
    let s = gen_expr env sub in
    (match s with
     | Imm n -> Imm (apply_unary op n)
     | Temp _ ->
       let t = fresh_temp env in
       emit env (IUnaryOp (t, op, s));
       Temp t)
  | Binary (lhs, And, rhs) -> gen_short_circuit env lhs rhs ~stop_on_zero:true
  | Binary (lhs, Or, rhs) -> gen_short_circuit env lhs rhs ~stop_on_zero:false
  | Binary (lhs, op, rhs) ->
    let l = gen_expr env lhs in
    let r = gen_expr env rhs in
    (match l, r with
     | Imm a, Imm b when apply_binary op a b <> None ->
       Imm (Option.get (apply_binary op a b))
     | _ ->
       let t = fresh_temp env in
       emit env (IBinOp (t, op, l, r));
       Temp t)
  | Call (name, args) ->
    let args = gen_args env args in
    let t = fresh_temp env in
    emit env (ICall (Some t, name, args));
    Temp t

(* [List.map] leaves evaluation order unspecified, but arguments may call
   functions with side effects, so they are lowered left to right explicitly. *)
and gen_args env = function
  | [] -> []
  | arg :: rest ->
    let operand = gen_expr env arg in
    operand :: gen_args env rest

(* [a && b] and [a || b] share a shape: evaluate [a], leave early with the
   short-circuit answer, otherwise the result is the truthiness of [b]. *)
and gen_short_circuit env lhs rhs ~stop_on_zero =
  let result = fresh_temp env in
  let short = fresh_label (if stop_on_zero then "and_false" else "or_true") in
  let l_end = fresh_label (if stop_on_zero then "and_end" else "or_end") in
  let branch operand =
    if stop_on_zero then IBranchZero (operand, short)
    else IBranchNonZero (operand, short)
  in
  let l = gen_expr env lhs in
  emit env (branch l);
  let r = gen_expr env rhs in
  emit env (branch r);
  emit env (ILoad (result, Imm (if stop_on_zero then 1 else 0)));
  emit env (IJump l_end);
  emit env (ILabel short);
  emit env (ILoad (result, Imm (if stop_on_zero then 0 else 1)));
  emit env (ILabel l_end);
  Temp result

let gen_store_var env name operand =
  match lookup_var env name with
  | Some (`Temp dst) ->
    if operand <> Temp dst then emit env (ILoad (dst, operand))
  | Some (`Global g) -> emit env (IStoreGlobal (g, operand))
  | _ -> emit env (IStoreGlobal (name, operand))

(* A declaration binds its name only after the initializer has been lowered, so
   [int x = x;] in an inner scope still reads the outer [x]. *)
let gen_decl env name e =
  let operand = gen_expr env e in
  let dst = fresh_temp env in
  emit env (ILoad (dst, operand));
  add_var env name (`Temp dst)

let rec gen_stmt env (s : stmt) : unit =
  match s with
  | Empty -> ()
  | ExprStmt (Call (name, args)) ->
    let args = gen_args env args in
    emit env (ICall (None, name, args))
  | ExprStmt e -> ignore (gen_expr env e)
  | Assign (name, e) ->
    let operand = gen_expr env e in
    gen_store_var env name operand
  | ConstDecl (name, e) -> gen_decl env name e
  | VarDecl (name, e) -> gen_decl env name e
  | Block body ->
    enter_scope env;
    List.iter (gen_stmt env) body;
    leave_scope env
  | If (cond, then_s, else_s) -> gen_if env cond then_s else_s
  | While (cond, body) -> gen_while env cond body
  | Break ->
    let (_, break_lbl) = Stack.top env.loop_stack in
    emit env (IJump break_lbl)
  | Continue ->
    let (cont_lbl, _) = Stack.top env.loop_stack in
    emit env (IJump cont_lbl)
  | Return None -> emit env (IReturn None)
  | Return (Some e) ->
    let operand = gen_expr env e in
    emit env (IReturn (Some operand))

and gen_if env cond then_s else_s =
  match else_s with
  | None ->
    let l_end = fresh_label "if_end" in
    let c = gen_expr env cond in
    emit env (IBranchZero (c, l_end));
    gen_stmt env then_s;
    emit env (ILabel l_end)
  | Some else_stmt ->
    let l_else = fresh_label "else" in
    let l_end = fresh_label "if_end" in
    let c = gen_expr env cond in
    emit env (IBranchZero (c, l_else));
    gen_stmt env then_s;
    emit env (IJump l_end);
    emit env (ILabel l_else);
    gen_stmt env else_stmt;
    emit env (ILabel l_end)

and gen_while env cond body =
  let l_cond = fresh_label "while_cond" in
  let l_end = fresh_label "while_end" in
  Stack.push (l_cond, l_end) env.loop_stack;
  emit env (ILabel l_cond);
  let c = gen_expr env cond in
  emit env (IBranchZero (c, l_end));
  gen_stmt env body;
  emit env (IJump l_cond);
  emit env (ILabel l_end);
  ignore (Stack.pop env.loop_stack)

let gen_func (globals : (string * [`Const of int | `Var]) list) (fd : func_def) =
  let env = new_env () in
  List.iter (fun (name, kind) ->
    match kind with
    | `Const n -> add_var env name (`Const n)
    | `Var -> add_var env name (`Global name)
  ) globals;
  enter_scope env;
  List.iteri (fun index p ->
    let t = fresh_temp env in
    emit env (ILoadParam (t, index));
    add_var env p (`Temp t)
  ) fd.params;
  enter_scope env;
  List.iter (gen_stmt env) fd.body;
  leave_scope env;
  leave_scope env;
  (match fd.ret_type with
   | VoidRet ->
     (match env.instrs with
      | IReturn _ :: _ -> ()
      | _ -> emit env (IReturn None))
   | IntRet ->
     (* A missing return on a reachable path is rejected by semantic analysis,
        but the emitted function still needs a terminator to fall into. *)
     (match env.instrs with
      | IReturn _ :: _ -> ()
      | _ -> emit env (IReturn (Some (Imm 0)))));
  {
    name = fd.name;
    ret_type = fd.ret_type;
    params = fd.params;
    body = List.rev env.instrs;
    temp_count = env.next_temp;
  }

let rec eval_const_init globals = function
  | IntLit n -> i32 n
  | Var name ->
    (match List.assoc_opt name globals with
     | Some v -> v
     | None -> 0)
  | Unary (op, e) -> apply_unary op (eval_const_init globals e)
  (* OCaml's own && / || keep C short-circuit semantics here, so
     [const int x = 0 && (1 / 0);] folds to 0 instead of failing. *)
  | Binary (lhs, And, rhs) ->
    if eval_const_init globals lhs <> 0 && eval_const_init globals rhs <> 0
    then 1 else 0
  | Binary (lhs, Or, rhs) ->
    if eval_const_init globals lhs <> 0 || eval_const_init globals rhs <> 0
    then 1 else 0
  | Binary (lhs, op, rhs) ->
    let a = eval_const_init globals lhs in
    let b = eval_const_init globals rhs in
    (match apply_binary op a b with
     | Some v -> v
     | None -> failwith "division by zero in constant initializer")
  | Call _ -> invalid_arg "function call in global initializer"

let lower (cu : comp_unit) : program =
  let globals = ref [] in
  let global_info = ref [] in
  let global_values = ref [] in
  let funcs = ref [] in
  List.iter (fun tl ->
    match tl with
    | GlobalConstDecl (name, e) ->
      let value = eval_const_init !global_values e in
      globals := GConst (name, value) :: !globals;
      global_info := (name, `Const value) :: !global_info;
      global_values := (name, value) :: !global_values
    | GlobalVarDecl (name, e) ->
      let value = eval_const_init !global_values e in
      globals := GVar (name, value) :: !globals;
      global_info := (name, `Var) :: !global_info;
      global_values := (name, value) :: !global_values
    | FuncDef fd -> funcs := gen_func !global_info fd :: !funcs
  ) cu;
  { globals = List.rev !globals; funcs = List.rev !funcs }
