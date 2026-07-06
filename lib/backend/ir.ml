(** Intermediate representation for ToyC *)

open Ast

type program = {
  globals : global list;
  funcs : func list;
}

and global =
  | GConst of string * int
  | GVar of string

and func = {
  name : string;
  ret_type : func_ret_type;
  params : string list;
  body : instr list;
}

and instr =
  | Label of string
  | Comment of string

let lower (_cu : comp_unit) : program =
  failwith "TODO: lower AST to IR"
