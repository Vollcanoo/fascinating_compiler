open Ast

module StringMap = Map.Make (String)

type value =
  | Var
  | Const of int

type func_sig = {
  ret_type : func_ret_type;
  arity : int;
}

type scope = value StringMap.t

type t = {
  scopes : scope list;
  funcs : func_sig StringMap.t;
}

let empty = { scopes = [ StringMap.empty ]; funcs = StringMap.empty }

let enter_scope tbl = { tbl with scopes = StringMap.empty :: tbl.scopes }

let leave_scope = function
  | { scopes = _ :: rest; funcs } -> { scopes = rest; funcs }
  | { scopes = []; _ } -> invalid_arg "leave_scope: empty scope stack"

let current_scope = function
  | { scopes = scope :: _; _ } -> scope
  | { scopes = []; _ } -> invalid_arg "current_scope: empty scope stack"

let has_current_value name tbl = StringMap.mem name (current_scope tbl)

let add_value name value tbl =
  match tbl.scopes with
  | scope :: rest -> { tbl with scopes = StringMap.add name value scope :: rest }
  | [] -> invalid_arg "add_value: empty scope stack"

let rec find_value name = function
  | [] -> None
  | scope :: rest ->
    (match StringMap.find_opt name scope with
     | Some _ as found -> found
     | None -> find_value name rest)

let lookup_value name tbl = find_value name tbl.scopes

let has_func name tbl = StringMap.mem name tbl.funcs

let add_func name func tbl = { tbl with funcs = StringMap.add name func tbl.funcs }

let lookup_func name tbl = StringMap.find_opt name tbl.funcs

let has_global_value name tbl =
  match List.rev tbl.scopes with
  | global :: _ -> StringMap.mem name global
  | [] -> false
