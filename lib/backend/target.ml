(** RISC-V32 instruction-encoding facts.

    Both the optimizer and the code generator need to agree on which immediates
    the target can encode directly.  Keeping the answer in one place means the
    optimizer never hoists an immediate the backend was going to fold into the
    instruction anyway, and never leaves one behind that the backend has to
    materialise with [li] on every loop iteration. *)

open Ast

let fits12 value = value >= -2048 && value <= 2047

let min_i32 = Int32.to_int Int32.min_int
let max_i32 = Int32.to_int Int32.max_int

let is_power_of_two value = value > 0 && value land (value - 1) = 0

let log2 value =
  let rec loop shift value = if value = 1 then shift else loop (shift + 1) (value lsr 1) in
  loop 0 value

let bit_positions value =
  let rec loop bit value acc =
    if value = 0 then List.rev acc
    else loop (bit + 1) (value lsr 1) (if value land 1 = 1 then bit :: acc else acc)
  in
  loop 0 value []

(* =====================================================
   Multiplication by a constant
   ===================================================== *)

type mul_plan =
  | MulZero
  | MulIdentity
  | MulShift of int
  (* (x << k) + x and (x << k) - x cover every 2^k+1 and 2^k-1 factor *)
  | MulShiftAdd of int
  | MulShiftSub of int
  | MulTwoShifts of int * int
  | MulNegated of mul_plan

let rec positive_mul_plan imm =
  if is_power_of_two imm && log2 imm < 32 then Some (MulShift (log2 imm))
  else
    let rec try_shift shift =
      if shift >= 31 then None
      else
        let power = 1 lsl shift in
        if imm = power + 1 then Some (MulShiftAdd shift)
        else if imm = power - 1 then Some (MulShiftSub shift)
        else try_shift (shift + 1)
    in
    match try_shift 1 with
    | Some _ as plan -> plan
    | None ->
      (match bit_positions imm with
       | [first; second] when second < 32 -> Some (MulTwoShifts (first, second))
       | _ -> None)

and mul_plan imm =
  match imm with
  | 0 -> Some MulZero
  | 1 -> Some MulIdentity
  | -1 -> Some (MulNegated MulIdentity)
  | imm when imm > 0 -> positive_mul_plan imm
  | imm when imm <> min_i32 ->
    (match positive_mul_plan (-imm) with
     | Some plan -> Some (MulNegated plan)
     | None -> None)
  | _ -> None

let divides_by_shift imm =
  is_power_of_two imm || (imm <> min_i32 && imm < 0 && is_power_of_two (-imm))

(* =====================================================
   Which immediates ride along inside the instruction

   [immediate_is_free op side imm] answers: given [imm] as the [side] operand of
   [op], can the backend encode it without first loading it into a register?
   Zero is always free, because x0 reads as zero.
   ===================================================== *)

type side = Left | Right

let immediate_is_free op side imm =
  if imm = 0 then true
  else
    match op, side with
    | Add, _ -> fits12 imm
    | Sub, Right -> imm <> min_i32 && fits12 (-imm)
    | (Eq | Ne), _ -> false (* only the imm = 0 case above is free *)
    | Lt, Right | Ge, Right -> fits12 imm
    | (Le | Gt), Right -> imm <> max_i32 && fits12 (imm + 1)
    | Mul, _ -> mul_plan imm <> None
    | (Div | Mod), Right -> divides_by_shift imm
    | _ -> false
