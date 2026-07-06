(** Abstract Syntax Tree for ToyC *)

type comp_unit = top_level list

and top_level =
  | GlobalConstDecl of string * exp
  | GlobalVarDecl of string * exp
  | FuncDef of func_def

and func_def = {
  ret_type : func_ret_type;
  name : string;
  params : string list;
  body : block;
}

and func_ret_type =
  | IntRet
  | VoidRet

and block = stmt list

and stmt =
  | Block of block
  | Empty
  | ExprStmt of exp
  | Assign of string * exp
  | ConstDecl of string * exp
  | VarDecl of string * exp
  | If of exp * stmt * stmt option
  | While of exp * stmt
  | Break
  | Continue
  | Return of exp option

and exp =
  | IntLit of int
  | Var of string
  | Unary of unary_op * exp
  | Binary of exp * bin_op * exp
  | Call of string * exp list

and unary_op =
  | UPlus
  | UMinus
  | Not

and bin_op =
  | Or
  | And
  | Lt
  | Gt
  | Le
  | Ge
  | Eq
  | Ne
  | Add
  | Sub
  | Mul
  | Div
  | Mod

(** Debug pretty-printer *)

let rec string_of_comp_unit cu =
  String.concat "\n\n" (List.map string_of_top_level cu)

and string_of_top_level = function
  | GlobalConstDecl (name, e) -> "const int " ^ name ^ " = " ^ string_of_exp e ^ ";"
  | GlobalVarDecl (name, e) -> "int " ^ name ^ " = " ^ string_of_exp e ^ ";"
  | FuncDef fd -> string_of_func_def fd

and string_of_func_def fd =
  let ret =
    match fd.ret_type with
    | IntRet -> "int"
    | VoidRet -> "void"
  in
  let params = String.concat ", " (List.map (fun p -> "int " ^ p) fd.params) in
  ret ^ " " ^ fd.name ^ "(" ^ params ^ ") " ^ string_of_block fd.body

and string_of_block stmts =
  "{\n" ^ String.concat "\n" (List.map (fun s -> "  " ^ string_of_stmt s) stmts) ^ "\n}"

and string_of_stmt = function
  | Block b -> string_of_block b
  | Empty -> ";"
  | ExprStmt e -> string_of_exp e ^ ";"
  | Assign (name, e) -> name ^ " = " ^ string_of_exp e ^ ";"
  | ConstDecl (name, e) -> "const int " ^ name ^ " = " ^ string_of_exp e ^ ";"
  | VarDecl (name, e) -> "int " ^ name ^ " = " ^ string_of_exp e ^ ";"
  | If (cond, then_s, else_s) ->
    let base = "if (" ^ string_of_exp cond ^ ") " ^ string_of_stmt then_s in
    (match else_s with
     | None -> base
     | Some s -> base ^ " else " ^ string_of_stmt s)
  | While (cond, body) -> "while (" ^ string_of_exp cond ^ ") " ^ string_of_stmt body
  | Break -> "break;"
  | Continue -> "continue;"
  | Return None -> "return;"
  | Return (Some e) -> "return " ^ string_of_exp e ^ ";"

and string_of_exp = function
  | IntLit n -> string_of_int n
  | Var name -> name
  | Unary (op, e) -> string_of_unary_op op ^ string_of_exp e
  | Binary (e1, op, e2) ->
    "(" ^ string_of_exp e1 ^ " " ^ string_of_bin_op op ^ " " ^ string_of_exp e2 ^ ")"
  | Call (name, args) ->
    name ^ "(" ^ String.concat ", " (List.map string_of_exp args) ^ ")"

and string_of_unary_op = function
  | UPlus -> "+"
  | UMinus -> "-"
  | Not -> "!"

and string_of_bin_op = function
  | Or -> "||"
  | And -> "&&"
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | Eq -> "=="
  | Ne -> "!="
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
