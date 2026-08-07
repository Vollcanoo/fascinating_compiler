(** Reference interpreter for ToyC, evaluating the AST directly.

    It shares no code with the backend, so agreement between this interpreter
    and the simulated output of the generated assembly is real evidence that
    code generation is correct. Arithmetic wraps to 32 bits and division
    truncates toward zero, matching both C and RV32IM. *)

open Ast

exception Interp_error of string

let err fmt = Printf.ksprintf (fun s -> raise (Interp_error s)) fmt

let min32 = -2147483648

let wrap v =
  let v = v land 0xFFFFFFFF in
  if v land 0x80000000 <> 0 then v - 0x100000000 else v

exception Return_exc of int
exception Break_exc
exception Continue_exc

type ctx = {
  globals : (string, int ref) Hashtbl.t;
  funcs : (string, func_def) Hashtbl.t;
  mutable fuel : int;
}

let burn ctx =
  ctx.fuel <- ctx.fuel - 1;
  if ctx.fuel <= 0 then err "interpreter fuel exhausted (infinite loop?)"

let b2i b = if b then 1 else 0

let binop op x y =
  match op with
  | Add -> wrap (x + y)
  | Sub -> wrap (x - y)
  | Mul -> wrap (x * y)
  | Div ->
    if y = 0 then err "division by zero"
    else if x = min32 && y = -1 then min32
    else wrap (x / y)
  | Mod ->
    if y = 0 then err "modulo by zero"
    else if x = min32 && y = -1 then 0
    else wrap (x mod y)
  | Lt -> b2i (x < y)
  | Gt -> b2i (x > y)
  | Le -> b2i (x <= y)
  | Ge -> b2i (x >= y)
  | Eq -> b2i (x = y)
  | Ne -> b2i (x <> y)
  | And -> b2i (x <> 0 && y <> 0)
  | Or -> b2i (x <> 0 || y <> 0)

let lookup ctx scopes name =
  let rec find = function
    | [] ->
      (match Hashtbl.find_opt ctx.globals name with
       | Some r -> r
       | None -> err "unbound identifier %S" name)
    | frame :: rest ->
      (match List.assoc_opt name !frame with
       | Some r -> r
       | None -> find rest)
  in
  find !scopes

let rec eval ctx scopes (e : exp) : int =
  match e with
  | IntLit n -> wrap n
  | Var name -> !(lookup ctx scopes name)
  | Unary (UPlus, sub) -> eval ctx scopes sub
  | Unary (UMinus, sub) -> wrap (-eval ctx scopes sub)
  | Unary (Not, sub) -> b2i (eval ctx scopes sub = 0)
  | Binary (lhs, And, rhs) ->
    if eval ctx scopes lhs = 0 then 0 else b2i (eval ctx scopes rhs <> 0)
  | Binary (lhs, Or, rhs) ->
    if eval ctx scopes lhs <> 0 then 1 else b2i (eval ctx scopes rhs <> 0)
  | Binary (lhs, op, rhs) ->
    (* Bind left before right: the backend evaluates operands in this order,
       which is observable when an operand calls a function with a side
       effect. *)
    let x = eval ctx scopes lhs in
    let y = eval ctx scopes rhs in
    binop op x y
  | Call (name, args) ->
    let vals = List.map (eval ctx scopes) args in
    call ctx name vals

and exec ctx scopes (s : stmt) : unit =
  burn ctx;
  match s with
  | Empty -> ()
  | ExprStmt e -> ignore (eval ctx scopes e)
  | Assign (name, e) ->
    let v = eval ctx scopes e in
    lookup ctx scopes name := v
  | ConstDecl (name, e) | VarDecl (name, e) ->
    let v = eval ctx scopes e in
    (match !scopes with
     | frame :: _ -> frame := (name, ref v) :: !frame
     | [] -> err "declaration outside any scope")
  | Block body ->
    let frame = ref [] in
    scopes := frame :: !scopes;
    let restore () = scopes := List.tl !scopes in
    (try List.iter (exec ctx scopes) body with e -> restore (); raise e);
    restore ()
  | If (cond, then_s, else_s) ->
    if eval ctx scopes cond <> 0 then exec ctx scopes then_s
    else (match else_s with None -> () | Some s -> exec ctx scopes s)
  | While (cond, body) ->
    let continue_looping = ref true in
    while !continue_looping && eval ctx scopes cond <> 0 do
      burn ctx;
      (try exec ctx scopes body with
       | Continue_exc -> ()
       | Break_exc -> continue_looping := false)
    done
  | Break -> raise Break_exc
  | Continue -> raise Continue_exc
  | Return None -> raise (Return_exc 0)
  | Return (Some e) -> raise (Return_exc (eval ctx scopes e))

and call ctx name args : int =
  burn ctx;
  match Hashtbl.find_opt ctx.funcs name with
  | None -> err "call to unknown function %S" name
  | Some fd ->
    if List.length fd.params <> List.length args then
      err "arity mismatch calling %S" name;
    let frame = ref (List.map2 (fun p v -> (p, ref v)) fd.params args) in
    let scopes = ref [frame] in
    (try
       List.iter (exec ctx scopes) fd.body;
       0
     with Return_exc v -> v)

let run ?(fuel = 200_000_000) (cu : comp_unit) : int =
  let ctx =
    { globals = Hashtbl.create 16; funcs = Hashtbl.create 16; fuel }
  in
  let empty_scopes = ref [] in
  List.iter
    (fun tl ->
      match tl with
      | GlobalConstDecl (name, e) | GlobalVarDecl (name, e) ->
        let v = eval ctx empty_scopes e in
        Hashtbl.replace ctx.globals name (ref v)
      | FuncDef fd -> Hashtbl.replace ctx.funcs fd.name fd)
    cu;
  call ctx "main" []
