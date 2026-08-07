(** Minimal RV32IM interpreter covering the instruction subset our backend
    emits.

    This is test-only support code: it is never linked into the compiler
    binary. It exists because the development machine has no RISC-V toolchain,
    so generated assembly is verified by executing it here instead.

    Besides the exit code it reports the number of instructions retired, which
    serves as a machine-independent proxy for the runtime of generated code. *)

exception Sim_error of string

let err fmt = Printf.ksprintf (fun s -> raise (Sim_error s)) fmt

(* ---------------------------------------------------------------- *)
(* 32-bit arithmetic                                                  *)
(* ---------------------------------------------------------------- *)

let min32 = -2147483648

let wrap v =
  let v = v land 0xFFFFFFFF in
  if v land 0x80000000 <> 0 then v - 0x100000000 else v

let unsigned v = v land 0xFFFFFFFF

(* ---------------------------------------------------------------- *)
(* Registers                                                          *)
(* ---------------------------------------------------------------- *)

let reg_names =
  [| "zero"; "ra"; "sp"; "gp"; "tp"; "t0"; "t1"; "t2";
     "s0"; "s1"; "a0"; "a1"; "a2"; "a3"; "a4"; "a5";
     "a6"; "a7"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7";
     "s8"; "s9"; "s10"; "s11"; "t3"; "t4"; "t5"; "t6" |]

let reg_ra = 1
let reg_sp = 2
let reg_a0 = 10

let reg_index name =
  if name = "fp" then 8
  else begin
    let rec find i =
      if i = 32 then None
      else if reg_names.(i) = name then Some i
      else find (i + 1)
    in
    match find 0 with
    | Some i -> i
    | None ->
      let n = String.length name in
      if n >= 2 && name.[0] = 'x' then
        match int_of_string_opt (String.sub name 1 (n - 1)) with
        | Some i when i >= 0 && i < 32 -> i
        | _ -> err "unknown register %S" name
      else err "unknown register %S" name
  end

(* ---------------------------------------------------------------- *)
(* Memory layout                                                      *)
(* ---------------------------------------------------------------- *)

let mem_size = 1 lsl 22 (* 4 MiB *)
let data_base = 0x1000
let stack_top = mem_size - 16

(* ---------------------------------------------------------------- *)
(* Decoded instructions                                               *)
(* ---------------------------------------------------------------- *)

type instr =
  | Rop of string * int * int * int (* op, rd, rs1, rs2 *)
  | Iop of string * int * int * int (* op, rd, rs1, imm *)
  | Li of int * int (* rd, imm *)
  | La of int * int (* rd, absolute address *)
  | Lw of int * int * int (* rd, offset, base *)
  | Sw of int * int * int (* rs, offset, base *)
  | Jmp of int (* target instruction index *)
  | Br of string * int * int * int (* op, rs1, rs2, target *)
  | Call of int (* target instruction index *)
  | Ret

type program = {
  code : instr array;
  entry : int;
  mem : Bytes.t;
}

(* ---------------------------------------------------------------- *)
(* Assembler                                                          *)
(* ---------------------------------------------------------------- *)

let strip_comment line =
  match String.index_opt line '#' with
  | Some i -> String.sub line 0 i
  | None -> line

let is_label line =
  let n = String.length line in
  n > 1 && line.[n - 1] = ':'

let split_mnemonic line =
  match String.index_opt line ' ' with
  | Some i ->
    ( String.sub line 0 i,
      String.trim (String.sub line (i + 1) (String.length line - i - 1)) )
  | None ->
    (match String.index_opt line '\t' with
     | Some i ->
       ( String.sub line 0 i,
         String.trim (String.sub line (i + 1) (String.length line - i - 1)) )
     | None -> (line, ""))

let operands rest =
  if rest = "" then []
  else
    String.split_on_char ',' rest
    |> List.map String.trim
    |> List.filter (fun s -> s <> "")

let parse_imm s =
  match int_of_string_opt s with
  | Some v -> v
  | None -> err "bad immediate %S" s

(* "off(base)" or "(base)" *)
let parse_mem_operand s =
  match String.index_opt s '(' with
  | None -> err "bad memory operand %S" s
  | Some i ->
    let close =
      match String.index_opt s ')' with
      | Some j -> j
      | None -> err "bad memory operand %S" s
    in
    let off_str = String.trim (String.sub s 0 i) in
    let base = String.trim (String.sub s (i + 1) (close - i - 1)) in
    let off = if off_str = "" then 0 else parse_imm off_str in
    (off, reg_index base)

let align_up v a = (v + a - 1) / a * a

let assemble (text : string) : program =
  let lines =
    String.split_on_char '\n' text
    |> List.map (fun l -> String.trim (strip_comment l))
    |> List.filter (fun l -> l <> "")
  in
  let labels = Hashtbl.create 64 in
  let symbols = Hashtbl.create 16 in
  let mem = Bytes.make mem_size '\000' in

  (* Pass 1: assign addresses to code labels and lay out the data section. *)
  let section = ref `Text in
  let pc = ref 0 in
  let dp = ref data_base in
  List.iter
    (fun line ->
      if is_label line then begin
        let name = String.sub line 0 (String.length line - 1) in
        match !section with
        | `Text -> Hashtbl.replace labels name !pc
        | `Data -> Hashtbl.replace symbols name !dp
      end
      else if line.[0] = '.' then begin
        let d, rest = split_mnemonic line in
        match d with
        | ".text" -> section := `Text
        | ".data" | ".bss" | ".rodata" -> section := `Data
        | ".align" ->
          let n = parse_imm (String.trim rest) in
          dp := align_up !dp (1 lsl n)
        | ".p2align" ->
          let n = parse_imm (String.trim rest) in
          dp := align_up !dp (1 lsl n)
        | ".word" | ".long" | ".4byte" -> dp := !dp + 4
        | ".zero" | ".space" -> dp := !dp + parse_imm (String.trim rest)
        | ".globl" | ".global" | ".type" | ".size" | ".section" | ".file"
        | ".ident" | ".attribute" | ".option" ->
          ()
        | other -> err "unsupported directive %S" other
      end
      else incr pc)
    lines;

  (* Pass 2: fill in data words and decode instructions. *)
  let section = ref `Text in
  let dp = ref data_base in
  let code = ref [] in
  let resolve name =
    match Hashtbl.find_opt labels name with
    | Some i -> i
    | None -> err "undefined code label %S" name
  in
  let resolve_sym name =
    match Hashtbl.find_opt symbols name with
    | Some a -> a
    | None -> err "undefined data symbol %S" name
  in
  let store_word addr v =
    let v = unsigned v in
    Bytes.set mem addr (Char.chr (v land 0xFF));
    Bytes.set mem (addr + 1) (Char.chr ((v lsr 8) land 0xFF));
    Bytes.set mem (addr + 2) (Char.chr ((v lsr 16) land 0xFF));
    Bytes.set mem (addr + 3) (Char.chr ((v lsr 24) land 0xFF))
  in
  List.iter
    (fun line ->
      if is_label line then ()
      else if line.[0] = '.' then begin
        let d, rest = split_mnemonic line in
        match d with
        | ".text" -> section := `Text
        | ".data" | ".bss" | ".rodata" -> section := `Data
        | ".align" | ".p2align" ->
          let n = parse_imm (String.trim rest) in
          dp := align_up !dp (1 lsl n)
        | ".word" | ".long" | ".4byte" ->
          store_word !dp (parse_imm (String.trim rest));
          dp := !dp + 4
        | ".zero" | ".space" -> dp := !dp + parse_imm (String.trim rest)
        | _ -> ()
      end
      else begin
        let mnem, rest = split_mnemonic line in
        let ops = operands rest in
        let nth i =
          match List.nth_opt ops i with
          | Some s -> s
          | None -> err "%s: missing operand %d in %S" mnem i line
        in
        let r i = reg_index (nth i) in
        let im i = parse_imm (nth i) in
        let instr =
          match mnem with
          | "add" | "sub" | "mul" | "mulh" | "mulhu" | "div" | "divu" | "rem"
          | "remu" | "and" | "or" | "xor" | "sll" | "srl" | "sra" | "slt"
          | "sltu" ->
            Rop (mnem, r 0, r 1, r 2)
          | "sgt" -> Rop ("slt", r 0, r 2, r 1)
          | "sgtu" -> Rop ("sltu", r 0, r 2, r 1)
          | "addi" | "andi" | "ori" | "xori" | "slli" | "srli" | "srai"
          | "slti" | "sltiu" ->
            Iop (mnem, r 0, r 1, im 2)
          | "mv" -> Iop ("addi", r 0, r 1, 0)
          | "neg" -> Rop ("sub", r 0, 0, r 1)
          | "not" -> Iop ("xori", r 0, r 1, -1)
          | "seqz" -> Iop ("sltiu", r 0, r 1, 1)
          | "snez" -> Rop ("sltu", r 0, 0, r 1)
          | "sgtz" -> Rop ("slt", r 0, 0, r 1)
          | "sltz" -> Rop ("slt", r 0, r 1, 0)
          | "nop" -> Iop ("addi", 0, 0, 0)
          | "li" -> Li (r 0, im 1)
          | "lui" -> Li (r 0, wrap (im 1 lsl 12))
          | "la" -> La (r 0, resolve_sym (nth 1))
          | "lw" ->
            let off, base = parse_mem_operand (nth 1) in
            Lw (r 0, off, base)
          | "sw" ->
            let off, base = parse_mem_operand (nth 1) in
            Sw (r 0, off, base)
          | "j" -> Jmp (resolve (nth 0))
          | "tail" -> Jmp (resolve (nth 0))
          | "call" -> Call (resolve (nth 0))
          | "jal" ->
            if List.length ops = 1 then Call (resolve (nth 0))
            else Call (resolve (nth 1))
          | "ret" -> Ret
          | "jr" ->
            if r 0 = reg_ra then Ret else err "unsupported indirect jump %S" line
          | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" ->
            Br (mnem, r 0, r 1, resolve (nth 2))
          | "beqz" -> Br ("beq", r 0, 0, resolve (nth 1))
          | "bnez" -> Br ("bne", r 0, 0, resolve (nth 1))
          | "blez" -> Br ("bge", 0, r 0, resolve (nth 1))
          | "bgez" -> Br ("bge", r 0, 0, resolve (nth 1))
          | "bltz" -> Br ("blt", r 0, 0, resolve (nth 1))
          | "bgtz" -> Br ("blt", 0, r 0, resolve (nth 1))
          | "bgt" -> Br ("blt", r 1, r 0, resolve (nth 2))
          | "ble" -> Br ("bge", r 1, r 0, resolve (nth 2))
          | "bgtu" -> Br ("bltu", r 1, r 0, resolve (nth 2))
          | "bleu" -> Br ("bgeu", r 1, r 0, resolve (nth 2))
          | other -> err "unsupported instruction %S in %S" other line
        in
        code := instr :: !code
      end)
    lines;

  let entry =
    match Hashtbl.find_opt labels "main" with
    | Some i -> i
    | None -> err "no 'main' label in generated assembly"
  in
  { code = Array.of_list (List.rev !code); entry; mem }

(* ---------------------------------------------------------------- *)
(* Interpreter                                                        *)
(* ---------------------------------------------------------------- *)

type result = {
  exit_code : int;
  retired : int; (* instructions retired: proxy for runtime *)
}

let run ?(max_steps = 400_000_000) (prog : program) : result =
  let regs = Array.make 32 0 in
  let mem = prog.mem in
  let n_code = Array.length prog.code in
  regs.(reg_sp) <- stack_top;
  regs.(reg_ra) <- -1;
  let pc = ref prog.entry in
  let steps = ref 0 in
  let set rd v = if rd <> 0 then regs.(rd) <- wrap v in
  let check_addr addr =
    if addr < 0 || addr + 4 > mem_size then
      err "memory access out of range at 0x%x" addr;
    if addr land 3 <> 0 then err "misaligned access at 0x%x" addr
  in
  let load_word addr =
    check_addr addr;
    let b i = Char.code (Bytes.get mem (addr + i)) in
    wrap (b 0 lor (b 1 lsl 8) lor (b 2 lsl 16) lor (b 3 lsl 24))
  in
  let store_word addr v =
    check_addr addr;
    let v = unsigned v in
    Bytes.set mem addr (Char.chr (v land 0xFF));
    Bytes.set mem (addr + 1) (Char.chr ((v lsr 8) land 0xFF));
    Bytes.set mem (addr + 2) (Char.chr ((v lsr 16) land 0xFF));
    Bytes.set mem (addr + 3) (Char.chr ((v lsr 24) land 0xFF))
  in
  while !pc >= 0 do
    if !pc >= n_code then err "pc ran past end of code";
    if !steps >= max_steps then
      err "step limit exceeded after %d instructions (infinite loop?)" !steps;
    incr steps;
    let instr = prog.code.(!pc) in
    incr pc;
    match instr with
    | Rop (op, rd, a, b) ->
      let x = regs.(a) and y = regs.(b) in
      let v =
        match op with
        | "add" -> x + y
        | "sub" -> x - y
        | "mul" -> x * y
        | "mulh" -> (x * y) asr 32
        | "mulhu" -> (unsigned x * unsigned y) asr 32
        | "div" ->
          if y = 0 then -1
          else if x = min32 && y = -1 then min32
          else x / y
        | "divu" ->
          let x = unsigned x and y = unsigned y in
          if y = 0 then -1 else x / y
        | "rem" ->
          if y = 0 then x else if x = min32 && y = -1 then 0 else x mod y
        | "remu" ->
          let x = unsigned x and y = unsigned y in
          if y = 0 then x else x mod y
        | "and" -> x land y
        | "or" -> x lor y
        | "xor" -> x lxor y
        | "sll" -> x lsl (y land 31)
        | "srl" -> unsigned x lsr (y land 31)
        | "sra" -> x asr (y land 31)
        | "slt" -> if x < y then 1 else 0
        | "sltu" -> if unsigned x < unsigned y then 1 else 0
        | _ -> err "unhandled R-type %S" op
      in
      set rd v
    | Iop (op, rd, a, imm) ->
      let x = regs.(a) in
      let v =
        match op with
        | "addi" -> x + imm
        | "andi" -> x land imm
        | "ori" -> x lor imm
        | "xori" -> x lxor imm
        | "slli" -> x lsl (imm land 31)
        | "srli" -> unsigned x lsr (imm land 31)
        | "srai" -> x asr (imm land 31)
        | "slti" -> if x < imm then 1 else 0
        | "sltiu" -> if unsigned x < unsigned imm then 1 else 0
        | _ -> err "unhandled I-type %S" op
      in
      set rd v
    | Li (rd, imm) -> set rd imm
    | La (rd, addr) -> set rd addr
    | Lw (rd, off, base) -> set rd (load_word (regs.(base) + off))
    | Sw (rs, off, base) -> store_word (regs.(base) + off) regs.(rs)
    | Jmp target -> pc := target
    | Br (op, a, b, target) ->
      let x = regs.(a) and y = regs.(b) in
      let taken =
        match op with
        | "beq" -> x = y
        | "bne" -> x <> y
        | "blt" -> x < y
        | "bge" -> x >= y
        | "bltu" -> unsigned x < unsigned y
        | "bgeu" -> unsigned x >= unsigned y
        | _ -> err "unhandled branch %S" op
      in
      if taken then pc := target
    | Call target ->
      regs.(reg_ra) <- !pc;
      pc := target
    | Ret -> pc := regs.(reg_ra)
  done;
  { exit_code = regs.(reg_a0) land 0xFF; retired = !steps }

let simulate ?max_steps (asm : string) : result = run ?max_steps (assemble asm)
