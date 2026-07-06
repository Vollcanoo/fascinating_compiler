(** RISC-V32 code generation *)

open Ir

let emit (out : out_channel) (_prog : program) : unit =
  Printf.fprintf out "# TODO: RISC-V32 code generation\n";
  Printf.fprintf out ".text\n";
  Printf.fprintf out ".globl main\n";
  Printf.fprintf out "main:\n";
  Printf.fprintf out "  li a0, 0\n";
  Printf.fprintf out "  ret\n"
