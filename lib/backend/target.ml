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
   Division by a constant

   RV32 has no fast divider: div and rem run for tens of cycles while mulh
   costs a handful.  When the divisor is known, the quotient can be produced by
   multiplying by a fixed-point reciprocal instead.

   [magic d] is Hacker's Delight figure 10-1.  It searches for the smallest
   multiplier/shift pair for which

     (mulhs(M, n) [+/- n]) >> s, plus the sign bit

   equals n / d for *every* 32-bit n, which is what makes the substitution safe
   rather than merely usually right.  Arithmetic below is unsigned 32-bit, held
   in OCaml's wider native int and masked back at each step.
   ===================================================== *)

type magic = {
  multiplier : int;
  shift : int;
}

let magic d =
  let mask = 0xFFFFFFFF in
  let two31 = 0x80000000 in
  let truncate value = value land mask in
  let signed value = if value >= two31 then value - (mask + 1) else value in
  let ad = abs d in
  (* nc is the largest n with the same sign as d for which n mod d <> 0 *)
  let t = two31 + (if d < 0 then 1 else 0) in
  let anc = t - 1 - (t mod ad) in
  let p = ref 31 in
  let q1 = ref (two31 / anc) in
  let r1 = ref (two31 - (!q1 * anc)) in
  let q2 = ref (two31 / ad) in
  let r2 = ref (two31 - (!q2 * ad)) in
  let settled = ref false in
  while not !settled do
    incr p;
    q1 := truncate (!q1 * 2);
    r1 := truncate (!r1 * 2);
    if !r1 >= anc then begin
      q1 := truncate (!q1 + 1);
      r1 := !r1 - anc
    end;
    q2 := truncate (!q2 * 2);
    r2 := truncate (!r2 * 2);
    if !r2 >= ad then begin
      q2 := truncate (!q2 + 1);
      r2 := !r2 - ad
    end;
    let delta = ad - !r2 in
    settled := not (!q1 < delta || (!q1 = delta && !r1 = 0))
  done;
  let multiplier = truncate (!q2 + 1) in
  let multiplier = if d < 0 then truncate (- multiplier) else multiplier in
  { multiplier = signed multiplier; shift = !p - 32 }

(* Divisors the reciprocal trick does not cover: zero, the identities, and
   INT_MIN, whose magnitude has no 32-bit positive representation. *)
let division_magic d =
  if d = 0 || d = 1 || d = -1 || d = min_i32 then None
  else if is_power_of_two (abs d) then None
  else Some (magic d)

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
