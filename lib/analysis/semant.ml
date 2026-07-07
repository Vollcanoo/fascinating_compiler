(** Semantic analysis for ToyC *)

open Ast

module ST = Symbol_table

let error msg = failwith ("Semantic error: " ^ msg)

let expect_declared_value name tbl =
  match ST.lookup_value name tbl with
  | Some value -> value
  | None -> error ("use of undeclared identifier '" ^ name ^ "'")

let expect_declared_func name tbl =
  match ST.lookup_func name tbl with
  | Some fn -> fn
  | None -> error ("call to undeclared function '" ^ name ^ "'")

let declare_value name value tbl =
  if ST.has_current_value name tbl
  then error ("duplicate declaration of '" ^ name ^ "' in the same scope")
  else if ST.has_func name tbl
  then error ("declaration of '" ^ name ^ "' conflicts with a function")
  else ST.add_value name value tbl

let declare_global_value name value tbl =
  if ST.has_global_value name tbl || ST.has_func name tbl
  then error ("duplicate global declaration of '" ^ name ^ "'")
  else ST.add_value name value tbl

let declare_func fd tbl =
  if ST.has_func fd.name tbl || ST.has_global_value fd.name tbl
  then error ("duplicate function name '" ^ fd.name ^ "'")
  else ST.add_func fd.name { ST.ret_type = fd.ret_type; arity = List.length fd.params } tbl

let bool_of_int n = if n = 0 then 0 else 1

let eval_bin op a b =
  match op with
  | Or -> bool_of_int (bool_of_int a lor bool_of_int b)
  | And -> bool_of_int (bool_of_int a land bool_of_int b)
  | Lt -> bool_of_int (if a < b then 1 else 0)
  | Gt -> bool_of_int (if a > b then 1 else 0)
  | Le -> bool_of_int (if a <= b then 1 else 0)
  | Ge -> bool_of_int (if a >= b then 1 else 0)
  | Eq -> bool_of_int (if a = b then 1 else 0)
  | Ne -> bool_of_int (if a <> b then 1 else 0)
  | Add -> a + b
  | Sub -> a - b
  | Mul -> a * b
  | Div ->
    if b = 0 then error "division by zero in constant expression" else a / b
  | Mod ->
    if b = 0 then error "modulo by zero in constant expression" else a mod b

let rec eval_const_expr tbl = function
  | IntLit n -> n
  | Var name ->
    (match expect_declared_value name tbl with
     | ST.Const n -> n
     | ST.Var -> error ("variable '" ^ name ^ "' is not a compile-time constant"))
  | Unary (op, e) ->
    let v = eval_const_expr tbl e in
    (match op with
     | UPlus -> v
     | UMinus -> -v
     | Not -> bool_of_int (if v = 0 then 1 else 0))
  | Binary (lhs, op, rhs) ->
    let a = eval_const_expr tbl lhs in
    let b = eval_const_expr tbl rhs in
    eval_bin op a b
  | Call (name, _) -> error ("function call '" ^ name ^ "' is not a compile-time constant")

let rec check_expr tbl = function
  | IntLit _ -> ()
  | Var name -> ignore (expect_declared_value name tbl)
  | Unary (_, e) -> check_expr tbl e
  | Binary (lhs, _, rhs) ->
    check_expr tbl lhs;
    check_expr tbl rhs
  | Call (name, args) ->
    let fn = expect_declared_func name tbl in
    let actual = List.length args in
    if actual <> fn.ST.arity
    then
      error
        (Printf.sprintf
           "function '%s' expects %d argument(s), got %d"
           name
           fn.ST.arity
           actual);
    List.iter (check_expr tbl) args

type stmt_info = {
  returns : bool;
  may_break : bool;
}

let no_flow = { returns = false; may_break = false }

let rec check_stmt ret_type loop_depth tbl stmt =
  match stmt with
  | Empty -> tbl, no_flow
  | ExprStmt e ->
    check_expr tbl e;
    tbl, no_flow
  | Assign (name, e) ->
    (match expect_declared_value name tbl with
     | ST.Const _ -> error ("cannot assign to constant '" ^ name ^ "'")
     | ST.Var -> ());
    check_expr tbl e;
    tbl, no_flow
  | ConstDecl (name, e) ->
    let value = eval_const_expr tbl e in
    declare_value name (ST.Const value) tbl, no_flow
  | VarDecl (name, e) ->
    check_expr tbl e;
    declare_value name ST.Var tbl, no_flow
  | Block body ->
    let _, info = check_block ret_type loop_depth (ST.enter_scope tbl) body in
    tbl, info
  | If (cond, then_stmt, else_stmt) ->
    check_expr tbl cond;
    let _, then_info = check_stmt ret_type loop_depth tbl then_stmt in
    let else_info =
      match else_stmt with
      | None -> no_flow
      | Some s -> snd (check_stmt ret_type loop_depth tbl s)
    in
    ( tbl,
      {
        returns = then_info.returns && else_info.returns;
        may_break = then_info.may_break || else_info.may_break;
      } )
  | While (cond, body) ->
    check_expr tbl cond;
    let _, body_info = check_stmt ret_type (loop_depth + 1) tbl body in
    let returns =
      match (try Some (eval_const_expr tbl cond) with Failure _ -> None) with
      | Some n -> n <> 0 && body_info.returns && not body_info.may_break
      | None -> false
    in
    tbl, { returns; may_break = false }
  | Break ->
    if loop_depth = 0 then error "'break' used outside of a loop";
    tbl, { returns = false; may_break = true }
  | Continue ->
    if loop_depth = 0 then error "'continue' used outside of a loop";
    tbl, no_flow
  | Return None ->
    (match ret_type with
     | IntRet -> error "int function must return a value"
     | VoidRet -> ());
    tbl, { returns = true; may_break = false }
  | Return (Some e) ->
    (match ret_type with
     | VoidRet -> error "void function cannot return a value"
     | IntRet -> ());
    check_expr tbl e;
    tbl, { returns = true; may_break = false }

and check_block ret_type loop_depth tbl stmts =
  let rec loop tbl returns may_break = function
    | [] -> ST.leave_scope tbl, { returns; may_break }
    | stmt :: rest ->
      let tbl, info = check_stmt ret_type loop_depth tbl stmt in
      loop tbl (returns || info.returns) (may_break || info.may_break) rest
  in
  loop tbl false false stmts

let declare_params params tbl =
  List.fold_left
    (fun tbl name -> declare_value name ST.Var tbl)
    (ST.enter_scope tbl)
    params

let check_func tbl fd =
  let body_tbl = declare_params fd.params tbl in
  let _, info = check_block fd.ret_type 0 body_tbl fd.body in
  match fd.ret_type with
  | IntRet ->
    if not info.returns then error ("int function '" ^ fd.name ^ "' may not return a value")
  | VoidRet -> ()

let check_main tbl =
  match ST.lookup_func "main" tbl with
  | Some { ST.ret_type = IntRet; arity = 0 } -> ()
  | Some _ -> error "entry point must be 'int main()'"
  | None -> error "missing entry point 'int main()'"

let check (cu : comp_unit) : unit =
  let rec loop tbl = function
    | [] ->
      check_main tbl;
      ()
    | GlobalConstDecl (name, e) :: rest ->
      let value = eval_const_expr tbl e in
      loop (declare_global_value name (ST.Const value) tbl) rest
    | GlobalVarDecl (name, e) :: rest ->
      check_expr tbl e;
      loop (declare_global_value name ST.Var tbl) rest
    | FuncDef fd :: rest ->
      let tbl = declare_func fd tbl in
      check_func tbl fd;
      loop tbl rest
  in
  loop ST.empty cu
