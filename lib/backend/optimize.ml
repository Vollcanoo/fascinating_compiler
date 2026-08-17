(** Optimization pipeline for the ToyC IR.

    Everything here is a static program transformation driven by the AST, the
    IR and control/data-flow facts.  The compiler never runs the program it is
    compiling: constants are only evaluated when every operand has been *proven*
    constant, and calls and side effecting operations are never folded.

    Loops are the one case worth spelling out.  A loop whose body is pure
    straight-line arithmetic is replaced by the closed form of its recurrences
    (see [closed_form_loops] and [Scev]), which is symbolic algebra on the shape
    of the recurrence rather than a replay of it -- the work is proportional to
    the degree of the polynomial, not to the trip count.  A [main] built only
    out of such loops therefore does fold to a literal.  A body containing a
    call, a global store or control flow of its own does not qualify.

    Pass order (per function, run to a fixpoint):

      fold_assignment_temps  collapse "t = expr; x = t" into "x = expr"
      local_pass             constant/copy propagation, algebraic simplification,
                             strength reduction and local CSE
      propagate_constants    CFG-wide constant propagation with reachability
      cleanup_control_flow   redundant jumps, unreachable code, unused labels
      closed_form_loops      scalar evolution; counted loops with a pure body
      global_cse             available expressions across blocks
      licm                   loop-invariant code motion
      eliminate_dead_defs    liveness-driven dead definition removal
      eliminate_dead_stores  redundant global stores
      cleanup_control_flow

    Then once, after the fixpoint has settled: unroll_loops.

    Around that, per program: loop rotation, small-function inlining,
    tail-recursion to loop rewriting and unreachable function removal. *)

open Ir
module A = Ast
module IntMap = Map.Make (Int)
module IntSet = Cfg.IntSet
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

(* =====================================================
   Shared helpers
   ===================================================== *)

let is_power_of_two value = value > 0 && value land (value - 1) = 0

let log2 value =
  let rec loop shift value = if value = 1 then shift else loop (shift + 1) (value lsr 1) in
  loop 0 value

let same_operand lhs rhs =
  match lhs, rhs with
  | Imm a, Imm b -> a = b
  | Temp a, Temp b -> a = b
  | _ -> false

let commutative = function
  | A.Add | A.Mul | A.Eq | A.Ne | A.And | A.Or -> true
  | A.Sub | A.Div | A.Mod | A.Lt | A.Gt | A.Le | A.Ge -> false

(* Commutative operands are ordered so that an immediate always ends up on the
   right.  That gives CSE a single key per expression and lets the backend reach
   for addi/slti without a second set of patterns. *)
let canonical_binop op lhs rhs =
  if not (commutative op) then (lhs, rhs)
  else
    match lhs, rhs with
    | Imm _, Temp _ -> (rhs, lhs)
    | Temp a, Temp b when b < a -> (rhs, lhs)
    | _ -> (lhs, rhs)

let move_or_nop dst operand =
  if operand = Temp dst then [] else [ILoad (dst, operand)]

let unary_instr dst op operand =
  match operand with
  | Imm value -> [ILoad (dst, Imm (apply_unary op value))]
  | Temp _ -> [IUnaryOp (dst, op, operand)]

let terminates_block = function
  | ILabel _ | IJump _ | IBranchZero _ | IBranchNonZero _ | IReturn _ -> true
  | _ -> false

let has_call body = List.exists (function ICall _ -> true | _ -> false) body

let labels_in_body body =
  List.fold_left (fun labels -> function
    | ILabel label -> StringSet.add label labels
    | _ -> labels
  ) StringSet.empty body

(* =====================================================
   Algebraic simplification and strength reduction
   ===================================================== *)

let simplify_binary dst op lhs rhs =
  let lhs, rhs = canonical_binop op lhs rhs in
  match lhs, rhs with
  | Imm a, Imm b ->
    (match apply_binary op a b with
     | Some value -> [ILoad (dst, Imm value)]
     | None -> [IBinOp (dst, op, lhs, rhs)])
  | _ ->
    (match op, lhs, rhs with
     | A.Add, operand, Imm 0 -> move_or_nop dst operand
     | A.Sub, operand, Imm 0 -> move_or_nop dst operand
     | A.Sub, Imm 0, operand -> unary_instr dst A.UMinus operand
     | A.Sub, _, _ when same_operand lhs rhs -> [ILoad (dst, Imm 0)]
     | A.Mul, _, Imm 0 -> [ILoad (dst, Imm 0)]
     | A.Mul, operand, Imm 1 -> move_or_nop dst operand
     | A.Mul, operand, Imm (-1) -> unary_instr dst A.UMinus operand
     | A.Mul, operand, Imm value when is_power_of_two value && log2 value < 32 ->
       [IShiftLeft (dst, operand, log2 value)]
     | A.Add, _, _ when same_operand lhs rhs -> [IShiftLeft (dst, lhs, 1)]
     | A.Div, operand, Imm 1 -> move_or_nop dst operand
     | A.Div, operand, Imm (-1) -> unary_instr dst A.UMinus operand
     | A.Div, Imm 0, _ -> [ILoad (dst, Imm 0)]
     | A.Mod, _, Imm 1 | A.Mod, _, Imm (-1) | A.Mod, Imm 0, _ ->
       [ILoad (dst, Imm 0)]
     | (A.Eq | A.Le | A.Ge), _, _ when same_operand lhs rhs -> [ILoad (dst, Imm 1)]
     | (A.Ne | A.Lt | A.Gt), _, _ when same_operand lhs rhs -> [ILoad (dst, Imm 0)]
     | A.And, _, Imm 0 -> [ILoad (dst, Imm 0)]
     | A.And, operand, Imm _ -> [IBinOp (dst, A.Ne, operand, Imm 0)]
     | A.Or, _, Imm value when value <> 0 -> [ILoad (dst, Imm 1)]
     | A.Or, operand, Imm 0 -> [IBinOp (dst, A.Ne, operand, Imm 0)]
     | _ -> [IBinOp (dst, op, lhs, rhs)])

let simplify_shift dst operand amount =
  match operand with
  | Imm value -> [ILoad (dst, Imm (apply_shift_left value amount))]
  | Temp _ when amount = 0 -> move_or_nop dst operand
  | Temp _ -> [IShiftLeft (dst, operand, amount)]

let simplify_bit_and dst operand mask =
  match operand with
  | Imm value -> [ILoad (dst, Imm (value land mask))]
  | Temp _ -> [IBitAnd (dst, operand, mask)]

let simplify_shift_right_arith dst operand amount =
  match operand with
  | Imm value -> [ILoad (dst, Imm (apply_shift_right_arith value amount))]
  | Temp _ when amount = 0 -> move_or_nop dst operand
  | Temp _ -> [IShiftRightArith (dst, operand, amount)]

let simplify_shift_right_logic dst operand amount =
  match operand with
  | Imm value -> [ILoad (dst, Imm (apply_shift_right_logic value amount))]
  | Temp _ when amount = 0 -> move_or_nop dst operand
  | Temp _ -> [IShiftRightLogic (dst, operand, amount)]

let simplify_mul_high dst lhs rhs =
  match lhs, rhs with
  | Imm a, Imm b -> [ILoad (dst, Imm (apply_mul_high a b))]
  | (Imm 0, _ | _, Imm 0) -> [ILoad (dst, Imm 0)]
  | _ -> [IMulHigh (dst, lhs, rhs)]

(* =====================================================
   Values that cannot be negative

   Truncation towards zero is what makes signed division expensive: "x / 2^k"
   needs a bias added before the shift, "x % 2^k" needs that plus a subtract,
   and the reciprocal sequence needs a final sign correction.  Every one of
   those steps is dead code when the dividend cannot be negative.

   Two sources are worth proving.  The first is structural: masks, comparison
   results and non-negative constants.  The second is loop counters, which is
   where it actually pays, and which needs an argument about overflow rather
   than just about the initial value.
   ===================================================== *)

(* A loop counter is non-negative for the whole loop when it starts non-negative,
   only ever grows, and the loop test keeps it under a constant ceiling low
   enough that the next increment cannot wrap into the negatives.  Drop any of
   those three and the guarantee is gone: an unbounded counter eventually
   overflows, and overflow is exactly the case being relied upon not to happen. *)
type counted_loop = {
  loop_header : int;
  loop_nodes : IntSet.t;
  counter : int;
  step : int;
  update_index : int;
}

let counted_loops body =
  let cfg = Cfg.build body in
  let count = Array.length cfg.instrs in
  let doms = Cfg.dominators cfg in
  let indices = List.init count (fun i -> i) in
  let definitions t = List.filter (fun i -> instr_dest cfg.instrs.(i) = Some t) indices in
  let counters = ref [] in
  List.iter (fun (header, latch) ->
    let nodes = Cfg.natural_loop cfg header latch in
    let starts_non_negative index =
      match cfg.instrs.(index) with ILoad (_, Imm n) -> n >= 0 | _ -> false
    in
    (* Cfg.successors puts a branch's taken edge first, so this is the back edge. *)
    let branches_to_header =
      match cfg.succs.(latch) with taken :: _ -> taken = header | [] -> false
    in
    match cfg.instrs.(latch) with
    | IBranchNonZero (Temp condition, _) when branches_to_header ->
      (* Loop rotation duplicates the condition, so the test temporary has a
         definition in the preheader as well.  The one that reaches the latch is
         the one inside the loop that dominates it. *)
      (match
         List.filter
           (fun i -> IntSet.mem i nodes && Cfg.dominates doms i latch)
           (definitions condition)
       with
       | [test] ->
         (match cfg.instrs.(test) with
          | IBinOp (_, (A.Lt | A.Le), Temp tested, Imm ceiling) ->
            (* When the increment is shared with another use it survives as
               "t = i + step; i = t", and copy propagation then rewrites the
               test to read t rather than i.  So the counter is either the
               tested value itself or something the tested value is copied
               into. *)
            let candidates =
              tested
              :: List.filter_map (fun index ->
                match cfg.instrs.(index) with
                | ILoad (dst, Temp source) when source = tested && IntSet.mem index nodes ->
                  Some dst
                | _ -> None) indices
            in
            let try_counter counter =
              let inside, outside =
                List.partition (fun i -> IntSet.mem i nodes) (definitions counter)
              in
              let increment_step = function
                | IBinOp (_, A.Add, Temp base, Imm step) when base = counter -> Some step
                | _ -> None
              in
              let step_of index =
                match cfg.instrs.(index) with
                | ILoad (_, Temp source) when source <> counter ->
                  (match
                     List.filter (fun d -> IntSet.mem d nodes) (definitions source)
                   with
                   | [definition] -> increment_step cfg.instrs.(definition)
                   | _ -> None)
                | instr -> increment_step instr
              in
              match inside with
              | [update] ->
                (match step_of update with
                 | Some step
                   when step > 0
                        (* The body only runs while the counter is under the
                           ceiling, so its largest value is ceiling + step. *)
                        && ceiling <= max_i32 - step
                        && outside <> []
                        && List.for_all starts_non_negative outside ->
                   Some
                     { loop_header = header; loop_nodes = nodes; counter; step;
                       update_index = update }
                 | _ -> None)
              | _ -> None
            in
            (match List.find_map try_counter candidates with
             | Some loop -> counters := loop :: !counters
             | None -> ())
          | _ -> ())
       | _ -> ())
    | _ -> ()
  ) (Cfg.back_edges cfg doms);
  !counters

let counted_loop_counters body =
  List.fold_left (fun set loop -> IntSet.add loop.counter set) IntSet.empty
    (counted_loops body)

(* Flow-insensitive: a temporary counts as non-negative only when every
   definition of it produces a non-negative value.  Coarse, but sound, and it
   composes -- a mask of a counter is still non-negative. *)
let non_negative_temps body =
  let definitions = Hashtbl.create 64 in
  List.iter (fun instr ->
    match instr_dest instr with
    | Some dst ->
      Hashtbl.replace definitions dst (instr :: (Hashtbl.find_opt definitions dst |> Option.value ~default:[]))
    | None -> ()
  ) body;
  let known = ref (counted_loop_counters body) in
  let operand_known = function
    | Imm n -> n >= 0
    | Temp t -> IntSet.mem t !known
  in
  let produces = function
    | ILoad (_, operand) -> operand_known operand
    | IBitAnd (_, _, mask) -> mask >= 0
    (* A logical shift by at least one clears the sign bit. *)
    | IShiftRightLogic (_, _, amount) -> amount >= 1
    | IShiftRightArith (_, operand, _) -> operand_known operand
    (* Comparisons and the logical connectives yield 0 or 1. *)
    | IBinOp (_, (A.Lt | A.Gt | A.Le | A.Ge | A.Eq | A.Ne | A.And | A.Or), _, _) -> true
    (* A remainder takes the sign of its dividend, whatever the divisor's. *)
    | IBinOp (_, A.Mod, dividend, _) -> operand_known dividend
    | IBinOp (_, A.Div, dividend, Imm d) -> d > 0 && operand_known dividend
    | _ -> false
  in
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun t defs ->
      if (not (IntSet.mem t !known)) && List.for_all produces defs then begin
        known := IntSet.add t !known;
        changed := true
      end
    ) definitions
  done;
  !known

(* =====================================================
   Division and remainder by a constant

   Expanding the reciprocal sequence here rather than in the backend is what
   lets the rest of the pipeline see it: common subexpression elimination
   shares the sign correction between a "/ k" and a "% k" on the same value,
   and the multiplier itself becomes an ordinary loop-invariant constant that
   gets hoisted out of the loop.
   ===================================================== *)

let quotient_instrs fresh ~non_negative dst dividend d =
  let magnitude = abs d in
  if Target.is_power_of_two magnitude then begin
    let amount = Target.log2 magnitude in
    let shift_down target =
      if non_negative then
        (* Nothing to round: a non-negative dividend shifts straight down. *)
        [IShiftRightArith (target, dividend, amount)]
      else
        (* Truncation towards zero means a negative dividend needs the 2^k-1
           bias added before the arithmetic shift. *)
        let sign = fresh () and bias = fresh () and biased = fresh () in
        [ IShiftRightArith (sign, dividend, 31);
          IShiftRightLogic (bias, Temp sign, 32 - amount);
          IBinOp (biased, A.Add, dividend, Temp bias);
          IShiftRightArith (target, Temp biased, amount) ]
    in
    if d > 0 then shift_down dst
    else
      let magnitude_quotient = fresh () in
      shift_down magnitude_quotient
      @ [IUnaryOp (dst, A.UMinus, Temp magnitude_quotient)]
  end
  else
    match Target.division_magic d with
    | None -> [IBinOp (dst, A.Div, dividend, Imm d)]
    | Some { Target.multiplier; shift } ->
      let high = fresh () in
      let instrs = ref [IMulHigh (high, Imm multiplier, dividend)] in
      let current = ref high in
      let step build =
        let next = fresh () in
        instrs := !instrs @ [build next (Temp !current)];
        current := next
      in
      (* The reciprocal overflows into the sign bit for some divisors; the
         dividend is added back (or subtracted) to compensate. *)
      if d > 0 && multiplier < 0 then
        step (fun next source -> IBinOp (next, A.Add, source, dividend));
      if d < 0 && multiplier > 0 then
        step (fun next source -> IBinOp (next, A.Sub, source, dividend));
      if shift > 0 then
        step (fun next source -> IShiftRightArith (next, source, shift));
      (* The shift floors, and flooring only differs from truncation for a
         negative quotient.  A non-negative dividend over a positive divisor
         cannot produce one. *)
      if non_negative && d > 0 then !instrs @ move_or_nop dst (Temp !current)
      else
        let sign = fresh () in
        !instrs
        @ [ IShiftRightLogic (sign, Temp !current, 31);
            IBinOp (dst, A.Add, Temp !current, Temp sign) ]

let remainder_instrs fresh ~non_negative dst dividend d =
  let magnitude = abs d in
  if non_negative && Target.is_power_of_two magnitude then
    (* The remainder takes the sign of the dividend, so for a non-negative one
       the low bits are the whole answer whichever sign the divisor has. *)
    [IBitAnd (dst, dividend, magnitude - 1)]
  else
    let quotient = fresh () and product = fresh () in
    quotient_instrs fresh ~non_negative quotient dividend d
    (* The multiply by a constant is strength reduced to shifts on the next
       round, so this rarely stays a mul. *)
    @ [ IBinOp (product, A.Mul, Temp quotient, Imm d);
        IBinOp (dst, A.Sub, dividend, Temp product) ]

(* =====================================================
   Strength reduction of a loop counter's remainder

   "i % k" where i is a counter stepping by a constant is itself periodic: it
   walks 0, 1, ... k-1, 0, ... So instead of recomputing a reciprocal every
   iteration, carry the remainder alongside the counter and wrap it by hand.
   This is the modulo analogue of the classic strength reduction that turns
   "i * k" into an accumulator.

   Correctness rests on the counter being non-negative -- otherwise C's
   remainder changes sign and the running value would not track it -- and on
   0 < step < k, which is what makes a single conditional subtraction enough to
   bring the sum back into range.

   Only worth it when the remainder is expensive: a power-of-two modulus of a
   non-negative counter is already a single mask.
   ===================================================== *)

let strength_reduce_modulo_once body =
  let cfg = Cfg.build body in
  let modulus_in loop =
    IntSet.elements loop.loop_nodes
    |> List.find_map (fun index ->
      match cfg.instrs.(index) with
      | IBinOp (_, A.Mod, Temp t, Imm k)
        when t = loop.counter
             && abs k > 1
             && loop.step < abs k
             && not (Target.is_power_of_two (abs k)) -> Some (abs k)
      | _ -> None)
  in
  match List.find_map (fun loop ->
    match modulus_in loop with
    | Some modulus -> Some (loop, modulus)
    | None -> None
  ) (counted_loops body)
  with
  | None -> body
  | Some (loop, modulus) ->
    let next_temp = ref (max_temp body + 1) in
    let fresh () =
      let t = !next_temp in
      incr next_temp;
      t
    in
    let labels = labels_in_body body in
    let rec fresh_label base =
      if StringSet.mem base labels then fresh_label (base ^ "_next") else base
    in
    let wrapped = fresh_label (Printf.sprintf ".L_mod%d_wrapped" modulus) in
    let running = fresh () in
    let in_range = fresh () in
    (* Seeded once on entry with a real remainder; from then on it is carried. *)
    let seed = [IBinOp (running, A.Mod, Temp loop.counter, Imm modulus)] in
    let advance =
      [ IBinOp (running, A.Add, Temp running, Imm loop.step);
        IBinOp (in_range, A.Lt, Temp running, Imm modulus);
        IBranchNonZero (Temp in_range, wrapped);
        IBinOp (running, A.Sub, Temp running, Imm modulus);
        ILabel wrapped ]
    in
    body
    |> List.mapi (fun index instr ->
      if index = loop.loop_header then seed @ [instr]
      else if index = loop.update_index then instr :: advance
      else if IntSet.mem index loop.loop_nodes then
        match instr with
        | IBinOp (dst, A.Mod, Temp t, Imm k)
          when t = loop.counter && abs k = modulus -> [ILoad (dst, Temp running)]
        | instr -> [instr]
      else [instr])
    |> List.concat

let strength_reduce_modulo body =
  let rec fix body =
    let next = strength_reduce_modulo_once body in
    if next = body then body else fix next
  in
  fix body

let expand_constant_division body =
  let next_temp = ref (max_temp body + 1) in
  let fresh () =
    let t = !next_temp in
    incr next_temp;
    t
  in
  let known_non_negative = non_negative_temps body in
  let non_negative = function
    | Imm n -> n >= 0
    | Temp t -> IntSet.mem t known_non_negative
  in
  (* Zero and the identities are already handled by algebraic simplification,
     and INT_MIN is left to the hardware instruction. *)
  let expandable d = d <> 0 && d <> 1 && d <> (-1) && d <> min_i32 in
  body
  |> List.concat_map (function
    | IBinOp (dst, A.Div, dividend, Imm d) when expandable d ->
      quotient_instrs fresh ~non_negative:(non_negative dividend) dst dividend d
    | IBinOp (dst, A.Mod, dividend, Imm d) when expandable d ->
      remainder_instrs fresh ~non_negative:(non_negative dividend) dst dividend d
    | instr -> [instr])

(* =====================================================
   Remainders that are only tested against zero

   "x % 2^k" needs a sign correction because C rounds towards zero, which costs
   six instructions.  But "x % 2^k == 0" holds exactly when the low k bits of x
   are clear, whatever the sign, so a single mask answers the question.  This
   only fires when *every* use of the remainder is a zero test.
   ===================================================== *)

let power_of_two_mask = function
  | Imm value when value <> min_i32 ->
    let magnitude = abs value in
    if Target.is_power_of_two magnitude then Some (magnitude - 1) else None
  | _ -> None

let only_tested_against_zero body t =
  let uses_t instr = List.exists (fun operand -> operand = Temp t) (instr_operands instr) in
  List.for_all (fun instr ->
    match instr with
    | IBinOp (_, (A.Eq | A.Ne), Temp u, Imm 0)
    | IBinOp (_, (A.Eq | A.Ne), Imm 0, Temp u)
    | IBranchZero (Temp u, _)
    | IBranchNonZero (Temp u, _) when u = t -> true
    | instr -> not (uses_t instr)
  ) body

let definition_counts body =
  List.fold_left (fun counts instr ->
    match instr_dest instr with
    | None -> counts
    | Some dst ->
      IntMap.add dst ((IntMap.find_opt dst counts |> Option.value ~default:0) + 1) counts
  ) IntMap.empty body

let rewrite_modulo_zero_tests body =
  let counts = definition_counts body in
  List.map (fun instr ->
    match instr with
    | IBinOp (dst, A.Mod, lhs, rhs) ->
      (match power_of_two_mask rhs with
       | Some mask
         when IntMap.find_opt dst counts = Some 1 && only_tested_against_zero body dst ->
         IBitAnd (dst, lhs, mask)
       | _ -> instr)
    | instr -> instr
  ) body

(* =====================================================
   Local pass: constant/copy propagation and local CSE
   ===================================================== *)

type value =
  | Const of int
  | Copy of int

type expr_key =
  | EUnary of A.unary_op * operand
  | EBinary of A.bin_op * operand * operand
  | EShift of operand * int
  | EShiftRightArith of operand * int
  | EShiftRightLogic of operand * int
  | EMulHigh of operand * operand
  | EBitAnd of operand * int

module ExprMap = Map.Make (struct
  type t = expr_key

  let compare = compare
end)

let rec value_depends_on env seen target = function
  | Const _ -> false
  | Copy t ->
    t = target
    || (not (IntSet.mem t seen)
        && (match IntMap.find_opt t env with
            | None -> false
            | Some value -> value_depends_on env (IntSet.add t seen) target value))

let kill_value t env =
  env
  |> IntMap.remove t
  |> IntMap.filter (fun _ value -> not (value_depends_on env IntSet.empty t value))

let define_value dst value env = IntMap.add dst value (kill_value dst env)

let rec resolve env seen t =
  if IntSet.mem t seen then Temp t
  else
    match IntMap.find_opt t env with
    | Some (Const value) -> Imm value
    | Some (Copy source) -> resolve env (IntSet.add t seen) source
    | None -> Temp t

let rewrite_operand env = function
  | Imm _ as imm -> imm
  | Temp t -> resolve env IntSet.empty t

let expr_of_instr = function
  | IUnaryOp (_, op, operand) -> Some (EUnary (op, operand))
  | IBinOp (_, op, lhs, rhs) ->
    let lhs, rhs = canonical_binop op lhs rhs in
    Some (EBinary (op, lhs, rhs))
  | IShiftLeft (_, operand, amount) -> Some (EShift (operand, amount))
  | IShiftRightArith (_, operand, amount) -> Some (EShiftRightArith (operand, amount))
  | IShiftRightLogic (_, operand, amount) -> Some (EShiftRightLogic (operand, amount))
  | IMulHigh (_, lhs, rhs) ->
    let lhs, rhs = canonical_binop A.Mul lhs rhs in
    Some (EMulHigh (lhs, rhs))
  | IBitAnd (_, operand, mask) -> Some (EBitAnd (operand, mask))
  | _ -> None

let expr_of_instrs = function
  | [instr] -> expr_of_instr instr
  | _ -> None

let expr_temps = function
  | EUnary (_, operand) | EShift (operand, _) | EBitAnd (operand, _)
  | EShiftRightArith (operand, _) | EShiftRightLogic (operand, _) ->
    (match operand_temp operand with Some t -> IntSet.singleton t | None -> IntSet.empty)
  | EBinary (_, lhs, rhs) | EMulHigh (lhs, rhs) ->
    List.filter_map operand_temp [lhs; rhs]
    |> List.fold_left (fun set t -> IntSet.add t set) IntSet.empty

let kill_exprs t exprs =
  ExprMap.filter
    (fun expr source -> source <> t && not (IntSet.mem t (expr_temps expr)))
    exprs

let apply_cse dst instrs exprs =
  match expr_of_instrs instrs with
  | None -> instrs
  | Some expr ->
    (match ExprMap.find_opt expr exprs with
     | Some source -> move_or_nop dst (Temp source)
     | None -> instrs)

let remember_expr dst instrs exprs =
  let exprs = kill_exprs dst exprs in
  match expr_of_instrs instrs with
  | Some expr when not (IntSet.mem dst (expr_temps expr)) -> ExprMap.add expr dst exprs
  | _ -> exprs

let value_of_rewritten dst = function
  | [ILoad (_, Imm value)] -> Some (Const value)
  | [ILoad (_, Temp t)] when t <> dst -> Some (Copy t)
  | _ -> None

(* The environment is valid along a straight-line run of instructions.  A label
   is a join point, so everything is dropped there; a conditional branch defines
   nothing, so the fall-through path keeps what it knew. *)
let local_pass body =
  let rec loop env exprs reachable acc = function
    | [] -> List.rev acc
    | ILabel label :: rest ->
      loop IntMap.empty ExprMap.empty true (ILabel label :: acc) rest
    | _ :: rest when not reachable -> loop env exprs false acc rest
    | instr :: rest ->
      let keep_defining dst instrs =
        let env =
          match value_of_rewritten dst instrs with
          | Some value -> define_value dst value env
          | None -> kill_value dst env
        in
        let exprs = remember_expr dst instrs exprs in
        loop env exprs true (List.rev_append instrs acc) rest
      in
      (match instr with
       | ILabel _ -> assert false
       | ILoadParam (dst, index) ->
         loop (kill_value dst env) (kill_exprs dst exprs) true
           (ILoadParam (dst, index) :: acc) rest
       | ILoadGlobal (dst, name) ->
         loop (kill_value dst env) (kill_exprs dst exprs) true
           (ILoadGlobal (dst, name) :: acc) rest
       | ILoad (dst, operand) ->
         let operand = rewrite_operand env operand in
         let instrs = move_or_nop dst operand in
         let env =
           match operand with
           | Temp t when t = dst -> env
           | Imm value -> define_value dst (Const value) env
           | Temp t -> define_value dst (Copy t) env
         in
         loop env (kill_exprs dst exprs) true (List.rev_append instrs acc) rest
       | IUnaryOp (dst, op, operand) ->
         let operand = rewrite_operand env operand in
         keep_defining dst (apply_cse dst (unary_instr dst op operand) exprs)
       | IBinOp (dst, op, lhs, rhs) ->
         let lhs = rewrite_operand env lhs in
         let rhs = rewrite_operand env rhs in
         keep_defining dst (apply_cse dst (simplify_binary dst op lhs rhs) exprs)
       | IShiftLeft (dst, operand, amount) ->
         let operand = rewrite_operand env operand in
         keep_defining dst (apply_cse dst (simplify_shift dst operand amount) exprs)
       | IBitAnd (dst, operand, mask) ->
         let operand = rewrite_operand env operand in
         keep_defining dst (apply_cse dst (simplify_bit_and dst operand mask) exprs)
       | IShiftRightArith (dst, operand, amount) ->
         let operand = rewrite_operand env operand in
         keep_defining dst
           (apply_cse dst (simplify_shift_right_arith dst operand amount) exprs)
       | IShiftRightLogic (dst, operand, amount) ->
         let operand = rewrite_operand env operand in
         keep_defining dst
           (apply_cse dst (simplify_shift_right_logic dst operand amount) exprs)
       | IMulHigh (dst, lhs, rhs) ->
         let lhs = rewrite_operand env lhs in
         let rhs = rewrite_operand env rhs in
         keep_defining dst (apply_cse dst (simplify_mul_high dst lhs rhs) exprs)
       | IStoreGlobal (name, operand) ->
         let operand = rewrite_operand env operand in
         loop env exprs true (IStoreGlobal (name, operand) :: acc) rest
       | ICall (dst, name, args) ->
         let args = List.map (rewrite_operand env) args in
         let env, exprs =
           match dst with
           | None -> (env, exprs)
           | Some dst -> (kill_value dst env, kill_exprs dst exprs)
         in
         loop env exprs true (ICall (dst, name, args) :: acc) rest
       | IBranchZero (operand, label) ->
         (match rewrite_operand env operand with
          | Imm 0 -> loop IntMap.empty ExprMap.empty false (IJump label :: acc) rest
          | Imm _ -> loop env exprs true acc rest
          | operand -> loop env exprs true (IBranchZero (operand, label) :: acc) rest)
       | IBranchNonZero (operand, label) ->
         (match rewrite_operand env operand with
          | Imm 0 -> loop env exprs true acc rest
          | Imm _ -> loop IntMap.empty ExprMap.empty false (IJump label :: acc) rest
          | operand -> loop env exprs true (IBranchNonZero (operand, label) :: acc) rest)
       | IJump label ->
         loop IntMap.empty ExprMap.empty false (IJump label :: acc) rest
       | IReturn operand ->
         let operand = Option.map (rewrite_operand env) operand in
         loop IntMap.empty ExprMap.empty false (IReturn operand :: acc) rest)
  in
  loop IntMap.empty ExprMap.empty true [] body

(* =====================================================
   Control flow cleanup
   ===================================================== *)

let remove_redundant_jumps body =
  let rec loop acc = function
    | IJump target :: ILabel label :: rest when target = label ->
      loop (ILabel label :: acc) rest
    (* "branch to the next label, otherwise jump away" is one inverted branch.
       Every "if (c) break;" and "if (c) continue;" lowers to this shape. *)
    | IBranchZero (operand, skipped) :: IJump target :: ILabel label :: rest
      when skipped = label ->
      loop (IBranchNonZero (operand, target) :: acc) (ILabel label :: rest)
    | IBranchNonZero (operand, skipped) :: IJump target :: ILabel label :: rest
      when skipped = label ->
      loop (IBranchZero (operand, target) :: acc) (ILabel label :: rest)
    | instr :: rest -> loop (instr :: acc) rest
    | [] -> List.rev acc
  in
  loop [] body

let remove_unreachable_instrs body =
  let cfg = Cfg.build body in
  let reachable = Cfg.reachable cfg in
  body
  |> List.mapi (fun index instr -> (index, instr))
  |> List.filter_map (fun (index, instr) ->
    if reachable.(index) then Some instr else None)

let referenced_labels body =
  List.fold_left (fun labels -> function
    | IJump label | IBranchZero (_, label) | IBranchNonZero (_, label) ->
      StringSet.add label labels
    | _ -> labels
  ) StringSet.empty body

let remove_unused_labels body =
  let labels = referenced_labels body in
  List.filter
    (function ILabel label -> StringSet.mem label labels | _ -> true)
    body

let cleanup_control_flow body =
  body
  |> remove_redundant_jumps
  |> remove_unreachable_instrs
  |> remove_redundant_jumps
  |> remove_unused_labels

(* =====================================================
   Dead code
   ===================================================== *)

let eliminate_dead_defs body =
  let rec fix body =
    let cfg = Cfg.build body in
    let liveness = Liveness.analyze cfg in
    let next =
      body
      |> List.mapi (fun index instr -> (index, instr))
      |> List.filter_map (fun (index, instr) ->
        let dead dst = not (IntSet.mem dst liveness.Liveness.live_out.(index)) in
        match instr with
        | ILoadParam (dst, _) | ILoad (dst, _) | ILoadGlobal (dst, _)
        | IUnaryOp (dst, _, _) | IBinOp (dst, _, _, _) | IShiftLeft (dst, _, _)
          when dead dst -> None
        (* A call has to stay, but it does not have to keep its result. *)
        | ICall (Some dst, name, args) when dead dst -> Some (ICall (None, name, args))
        | instr -> Some instr)
    in
    if List.length next = List.length body then next else fix next
  in
  fix body

(* A store to a global is dead when the same global is stored again before
   anything can observe it.  Anything that could branch, join or call resets the
   analysis, so this only fires inside a single straight-line run. *)
let eliminate_dead_stores body =
  let _, kept =
    List.fold_left (fun (overwritten, kept) instr ->
      match instr with
      | IStoreGlobal (name, _) ->
        if StringSet.mem name overwritten then (overwritten, kept)
        else (StringSet.add name overwritten, instr :: kept)
      | ILoadGlobal (_, name) -> (StringSet.remove name overwritten, instr :: kept)
      | ICall _ -> (StringSet.empty, instr :: kept)
      | instr when terminates_block instr -> (StringSet.empty, instr :: kept)
      | instr -> (overwritten, instr :: kept)
    ) (StringSet.empty, []) (List.rev body)
  in
  kept

(* =====================================================
   CFG-wide constant propagation
   ===================================================== *)

type lattice =
  | LUnknown
  | LConst of int
  | LOverdef

let lattice_equal lhs rhs =
  match lhs, rhs with
  | LUnknown, LUnknown | LOverdef, LOverdef -> true
  | LConst a, LConst b -> a = b
  | _ -> false

let merge_lattice lhs rhs =
  match lhs, rhs with
  | LUnknown, value | value, LUnknown -> value
  | LConst a, LConst b when a = b -> LConst a
  | _ -> LOverdef

let merge_env lhs rhs =
  IntMap.merge (fun _ lhs rhs ->
    match lhs, rhs with
    | None, None -> None
    | Some value, None | None, Some value -> Some value
    | Some lhs, Some rhs -> Some (merge_lattice lhs rhs)
  ) lhs rhs

let env_equal = IntMap.equal lattice_equal

let lattice_of env = function
  | Imm value -> LConst value
  | Temp t -> IntMap.find_opt t env |> Option.value ~default:LUnknown

let const_operand env = function
  | Imm _ as imm -> imm
  | Temp t as operand ->
    (match IntMap.find_opt t env with
     | Some (LConst value) -> Imm value
     | _ -> operand)

let transfer_const env instr =
  let define dst value = IntMap.add dst value env in
  match instr with
  | ILoadParam (dst, _) | ILoadGlobal (dst, _) -> define dst LOverdef
  | ILoad (dst, operand) -> define dst (lattice_of env operand)
  | IUnaryOp (dst, op, operand) ->
    define dst
      (match lattice_of env operand with
       | LConst value -> LConst (apply_unary op value)
       | other -> other)
  | IBinOp (dst, op, lhs, rhs) ->
    define dst
      (match lattice_of env lhs, lattice_of env rhs with
       | LConst a, LConst b ->
         (match apply_binary op a b with Some v -> LConst v | None -> LOverdef)
       | LOverdef, _ | _, LOverdef -> LOverdef
       | _ -> LUnknown)
  | IShiftLeft (dst, operand, amount) ->
    define dst
      (match lattice_of env operand with
       | LConst value -> LConst (apply_shift_left value amount)
       | other -> other)
  | IBitAnd (dst, operand, mask) ->
    define dst
      (match lattice_of env operand with
       | LConst value -> LConst (value land mask)
       | other -> other)
  | IShiftRightArith (dst, operand, amount) ->
    define dst
      (match lattice_of env operand with
       | LConst value -> LConst (apply_shift_right_arith value amount)
       | other -> other)
  | IShiftRightLogic (dst, operand, amount) ->
    define dst
      (match lattice_of env operand with
       | LConst value -> LConst (apply_shift_right_logic value amount)
       | other -> other)
  | IMulHigh (dst, lhs, rhs) ->
    define dst
      (match lattice_of env lhs, lattice_of env rhs with
       | LConst a, LConst b -> LConst (apply_mul_high a b)
       | LOverdef, _ | _, LOverdef -> LOverdef
       | _ -> LUnknown)
  | ICall (Some dst, _, _) -> define dst LOverdef
  | ICall (None, _, _) | IStoreGlobal _ | ILabel _ | IJump _ | IBranchZero _
  | IBranchNonZero _ | IReturn _ -> env

(* A branch whose condition is a known constant only has one live successor;
   ignoring the other is what makes this a *conditional* constant propagation
   and lets whole dead arms disappear. *)
let effective_succs env (cfg : Cfg.t) index =
  let taken_only () = match cfg.succs.(index) with target :: _ -> [target] | [] -> [] in
  let fallthrough_only () =
    match cfg.succs.(index) with _ :: next :: _ -> [next] | _ -> []
  in
  match cfg.instrs.(index) with
  | IBranchZero (operand, _) ->
    (match const_operand env operand with
     | Imm 0 -> taken_only ()
     | Imm _ -> fallthrough_only ()
     | _ -> cfg.succs.(index))
  | IBranchNonZero (operand, _) ->
    (match const_operand env operand with
     | Imm 0 -> fallthrough_only ()
     | Imm _ -> taken_only ()
     | _ -> cfg.succs.(index))
  | _ -> cfg.succs.(index)

let constant_dataflow body =
  let cfg = Cfg.build body in
  let count = Array.length cfg.instrs in
  let in_envs = Array.make count IntMap.empty in
  let out_envs = Array.make count IntMap.empty in
  let reachable = Array.make count false in
  if count > 0 then reachable.(0) <- true;
  let changed = ref true in
  while !changed do
    changed := false;
    for index = 0 to count - 1 do
      if reachable.(index) then begin
        let in_env =
          List.fold_left (fun env pred ->
            if reachable.(pred) then merge_env env out_envs.(pred) else env
          ) IntMap.empty cfg.preds.(index)
        in
        if not (env_equal in_env in_envs.(index)) then begin
          in_envs.(index) <- in_env;
          changed := true
        end;
        let out_env = transfer_const in_env cfg.instrs.(index) in
        if not (env_equal out_env out_envs.(index)) then begin
          out_envs.(index) <- out_env;
          changed := true
        end;
        List.iter (fun succ ->
          if not reachable.(succ) then begin
            reachable.(succ) <- true;
            changed := true
          end
        ) (effective_succs out_env cfg index)
      end
    done
  done;
  (cfg, in_envs, reachable)

let propagate_constants body =
  let cfg, in_envs, reachable = constant_dataflow body in
  cfg.instrs
  |> Array.to_list
  |> List.mapi (fun index instr -> (index, instr))
  |> List.filter_map (fun (index, instr) ->
    if not reachable.(index) then None
    else
      let env = in_envs.(index) in
      let folded = map_operands (const_operand env) instr in
      match folded with
      | IUnaryOp (dst, op, Imm value) -> Some (ILoad (dst, Imm (apply_unary op value)))
      | IBinOp (dst, op, Imm a, Imm b) ->
        (match apply_binary op a b with
         | Some value -> Some (ILoad (dst, Imm value))
         | None -> Some folded)
      | IShiftLeft (dst, Imm value, amount) ->
        Some (ILoad (dst, Imm (apply_shift_left value amount)))
      | IBitAnd (dst, Imm value, mask) -> Some (ILoad (dst, Imm (value land mask)))
      | IShiftRightArith (dst, Imm value, amount) ->
        Some (ILoad (dst, Imm (apply_shift_right_arith value amount)))
      | IShiftRightLogic (dst, Imm value, amount) ->
        Some (ILoad (dst, Imm (apply_shift_right_logic value amount)))
      | IMulHigh (dst, Imm a, Imm b) -> Some (ILoad (dst, Imm (apply_mul_high a b)))
      | IBranchZero (Imm 0, label) -> Some (IJump label)
      | IBranchZero (Imm _, _) -> None
      | IBranchNonZero (Imm 0, _) -> None
      | IBranchNonZero (Imm _, label) -> Some (IJump label)
      | instr -> Some instr)

(* =====================================================
   Global common subexpression elimination
   ===================================================== *)

let intersect_exprs lhs rhs =
  ExprMap.merge (fun _ lhs rhs ->
    match lhs, rhs with
    | Some lhs, Some rhs when lhs = rhs -> Some lhs
    | _ -> None
  ) lhs rhs

let transfer_exprs exprs instr =
  let exprs =
    match instr_dest instr with
    | None -> exprs
    | Some dst -> kill_exprs dst exprs
  in
  match expr_of_instr instr, instr_dest instr with
  | Some expr, Some dst when not (IntSet.mem dst (expr_temps expr)) ->
    ExprMap.add expr dst exprs
  | _ -> exprs

let global_cse body =
  let cfg = Cfg.build body in
  let count = Array.length cfg.instrs in
  let reachable = Cfg.reachable cfg in
  let in_exprs = Array.make count ExprMap.empty in
  let out_exprs = Array.make count ExprMap.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for index = 0 to count - 1 do
      if reachable.(index) then begin
        let in_expr =
          match
            cfg.preds.(index)
            |> List.filter (fun pred -> reachable.(pred))
            |> List.map (fun pred -> out_exprs.(pred))
          with
          | [] -> ExprMap.empty
          | first :: rest -> List.fold_left intersect_exprs first rest
        in
        if not (ExprMap.equal Int.equal in_expr in_exprs.(index)) then begin
          in_exprs.(index) <- in_expr;
          changed := true
        end;
        let out_expr = transfer_exprs in_expr cfg.instrs.(index) in
        if not (ExprMap.equal Int.equal out_expr out_exprs.(index)) then begin
          out_exprs.(index) <- out_expr;
          changed := true
        end
      end
    done
  done;
  cfg.instrs
  |> Array.to_list
  |> List.mapi (fun index instr -> (index, instr))
  |> List.filter_map (fun (index, instr) ->
    if not reachable.(index) then None
    else
      match expr_of_instr instr, instr_dest instr with
      | Some expr, Some dst ->
        (match ExprMap.find_opt expr in_exprs.(index) with
         | Some source when source <> dst -> Some (ILoad (dst, Temp source))
         | _ -> Some instr)
      | _ -> Some instr)

(* =====================================================
   Collapse "t = expr; x = t" when t dies immediately
   ===================================================== *)

let retarget_dest dst = function
  | ILoad (_, operand) -> ILoad (dst, operand)
  | IUnaryOp (_, op, operand) -> IUnaryOp (dst, op, operand)
  | IBinOp (_, op, lhs, rhs) -> IBinOp (dst, op, lhs, rhs)
  | IShiftLeft (_, operand, amount) -> IShiftLeft (dst, operand, amount)
  | IShiftRightArith (_, operand, amount) -> IShiftRightArith (dst, operand, amount)
  | IShiftRightLogic (_, operand, amount) -> IShiftRightLogic (dst, operand, amount)
  | IMulHigh (_, lhs, rhs) -> IMulHigh (dst, lhs, rhs)
  | IBitAnd (_, operand, mask) -> IBitAnd (dst, operand, mask)
  | ILoadGlobal (_, name) -> ILoadGlobal (dst, name)
  | ICall (Some _, name, args) -> ICall (Some dst, name, args)
  | instr -> instr

let retargetable = function
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IShiftRightArith _
  | IShiftRightLogic _ | IMulHigh _ | IBitAnd _ | ILoadGlobal _
  | ICall (Some _, _, _) -> true
  | _ -> false

let fold_assignment_temps body =
  let rec fix body =
    let cfg = Cfg.build body in
    let liveness = Liveness.analyze cfg in
    let rec loop index acc = function
      | producer :: ILoad (dst, Temp source) :: rest
        when retargetable producer
             && instr_dest producer = Some source
             && source <> dst
             && not (IntSet.mem source liveness.Liveness.live_out.(index + 1)) ->
        loop (index + 2) (retarget_dest dst producer :: acc) rest
      | instr :: rest -> loop (index + 1) (instr :: acc) rest
      | [] -> List.rev acc
    in
    let next = loop 0 [] body in
    if next = body then body else fix next
  in
  fix body

(* =====================================================
   Loop-invariant code motion
   ===================================================== *)

(* Division on RISC-V never traps, so every pure computation below is safe to
   speculate into the preheader. *)
let hoistable = function
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IShiftRightArith _
  | IShiftRightLogic _ | IMulHigh _ | IBitAnd _ -> true
  | ILoadParam _ | ILoadGlobal _ | IStoreGlobal _ | ICall _ | ILabel _
  | IJump _ | IBranchZero _ | IBranchNonZero _ | IReturn _ -> false

let licm_once body =
  let cfg = Cfg.build body in
  let count = Array.length cfg.instrs in
  let doms = Cfg.dominators cfg in
  let def_counts = definition_counts body in
  let single_definition t =
    IntMap.find_opt t def_counts |> Option.value ~default:0 = 1
  in
  let try_loop (header, latch) =
    let nodes = Cfg.natural_loop cfg header latch in
    let defs =
      IntSet.fold (fun node defs -> IntSet.union defs cfg.defs.(node)) nodes IntSet.empty
    in
    let written_globals, loop_has_call =
      IntSet.fold (fun node (written, calls) ->
        match cfg.instrs.(node) with
        | IStoreGlobal (name, _) -> (StringSet.add name written, calls)
        | ICall _ -> (written, true)
        | _ -> (written, calls)
      ) nodes (StringSet.empty, false)
    in
    let invariant = ref IntSet.empty in
    let hoisted = ref [] in
    let hoisted_indices = ref IntSet.empty in
    let operand_invariant = function
      | Imm _ -> true
      | Temp t -> (not (IntSet.mem t defs)) || IntSet.mem t !invariant
    in
    let changed = ref true in
    while !changed do
      changed := false;
      for index = 0 to count - 1 do
        if IntSet.mem index nodes && not (IntSet.mem index !hoisted_indices) then begin
          let instr = cfg.instrs.(index) in
          let movable =
            hoistable instr
            || (match instr with
                | ILoadGlobal (_, name) ->
                  (not loop_has_call) && not (StringSet.mem name written_globals)
                | _ -> false)
          in
          match instr_dest instr with
          | Some dst
            when movable
                 && single_definition dst
                 && List.for_all operand_invariant (instr_operands instr) ->
            hoisted := (index, instr) :: !hoisted;
            hoisted_indices := IntSet.add index !hoisted_indices;
            invariant := IntSet.add dst !invariant;
            changed := true
          | _ -> ()
        end
      done
    done;
    if !hoisted = [] then None
    else
      let ordered =
        !hoisted |> List.sort (fun (a, _) (b, _) -> compare a b) |> List.map snd
      in
      Some (header, !hoisted_indices, ordered)
  in
  match List.find_map try_loop (Cfg.back_edges cfg doms) with
  | None -> body
  | Some (header, hoisted_indices, hoisted) ->
    (* The header is the loop's label, so inserting in front of it lands in the
       preheader: reached on entry, skipped by the back edge. *)
    cfg.instrs
    |> Array.to_list
    |> List.mapi (fun index instr -> (index, instr))
    |> List.concat_map (fun (index, instr) ->
      if IntSet.mem index hoisted_indices then []
      else if index = header then hoisted @ [instr]
      else [instr])

let licm body =
  let rec fix body =
    let next = licm_once body in
    if next = body then body else fix next
  in
  fix body

(* =====================================================
   Promoting a global into a register across a loop

   A global read or written in a loop costs an address materialisation plus a
   memory access every iteration.  When nothing inside the loop can observe the
   memory location, the value can be loaded once into a register before the
   loop, worked on there, and written back on the way out.

   The conditions are what make the write-back reachable:

   - No call in the loop.  A callee could read or write the same global and
     would see a stale value.
   - No return in the loop.  A return would leave with the register holding the
     current value and memory still holding the old one.
   - Exactly one edge leaving the loop, and it leaves from the latch.  The
     write-back is placed on that edge, so a break or a continue — either of
     which shows up here as a second exiting edge — would jump straight past it.

   A guard that skips the whole loop is fine: it jumps past the pre-loop load
   as well, so nothing was ever cached.
   ===================================================== *)

let promote_loop_globals_once body =
  let cfg = Cfg.build body in
  let count = Array.length cfg.instrs in
  let doms = Cfg.dominators cfg in
  let try_loop (header, latch) =
    let nodes = Cfg.natural_loop cfg header latch in
    let leaves node = List.exists (fun succ -> not (IntSet.mem succ nodes)) cfg.succs.(node) in
    let exits =
      IntSet.fold (fun node acc ->
        List.fold_left
          (fun acc succ -> if IntSet.mem succ nodes then acc else IntSet.add succ acc)
          acc cfg.succs.(node)
      ) nodes IntSet.empty
    in
    let exiting = IntSet.filter leaves nodes in
    let observable =
      IntSet.exists (fun node ->
        match cfg.instrs.(node) with ICall _ | IReturn _ -> true | _ -> false) nodes
    in
    let written =
      IntSet.fold (fun node acc ->
        match cfg.instrs.(node) with
        | IStoreGlobal (name, _) -> StringSet.add name acc
        | _ -> acc
      ) nodes StringSet.empty
    in
    match
      cfg.instrs.(header), cfg.instrs.(latch),
      IntSet.elements exits, IntSet.elements exiting
    with
    | ILabel _, (IBranchZero _ | IBranchNonZero _), [exit], [exiting_node]
      when exiting_node = latch
           && exit = latch + 1
           && exit < count
           && not observable
           && not (StringSet.is_empty written) ->
      Some (header, latch, nodes, StringSet.elements written)
    | _ -> None
  in
  match List.find_map try_loop (Cfg.back_edges cfg doms) with
  | None -> body
  | Some (header, latch, nodes, globals) ->
    let next_temp = ref (max_temp body + 1) in
    let caches =
      List.map (fun name ->
        let t = !next_temp in
        incr next_temp;
        (name, t)
      ) globals
    in
    let cache name = List.assoc name caches in
    let loads = List.map (fun (name, t) -> ILoadGlobal (t, name)) caches in
    let writebacks = List.map (fun (name, t) -> IStoreGlobal (name, Temp t)) caches in
    body
    |> List.mapi (fun index instr ->
      let instr =
        if not (IntSet.mem index nodes) then instr
        else
          match instr with
          | ILoadGlobal (dst, name) when List.mem_assoc name caches ->
            ILoad (dst, Temp (cache name))
          | IStoreGlobal (name, operand) when List.mem_assoc name caches ->
            ILoad (cache name, operand)
          | instr -> instr
      in
      if index = header then loads @ [instr]
      else if index = latch then instr :: writebacks
      else [instr])
    |> List.concat

let promote_loop_globals body =
  let rec fix body =
    let next = promote_loop_globals_once body in
    if next = body then body else fix next
  in
  fix body

(* =====================================================
   Counted loop regions

   The two transformations below ask the same three questions of a loop: does it
   occupy one contiguous run of the instruction list, how many times does its
   body run, and is the counter guaranteed to start from the same value every
   time control enters the loop.

   The third one is the subtle one and the only one that can silently produce
   wrong code.  A trip count derived from "i starts at 0" is worthless if the
   loop can be re-entered with i already at its ceiling -- which is exactly the
   shape a nested loop takes when the inner counter is initialised outside the
   outer body rather than inside it.
   ===================================================== *)

type loop_region = {
  region_start : int;  (* the header label *)
  region_stop : int;   (* the branch at the bottom that goes back to it *)
  region_label : string;
  region_cond : int;   (* the temporary that branch tests *)
}

let branch_target = function
  | IJump target | IBranchZero (_, target) | IBranchNonZero (_, target) -> Some target
  | _ -> None

let label_references instrs label =
  let refs = ref [] in
  Array.iteri (fun index instr ->
    if branch_target instr = Some label then refs := index :: !refs) instrs;
  !refs

let label_indices instrs =
  let map = ref StringMap.empty in
  Array.iteri (fun index instr ->
    match instr with
    | ILabel label -> map := StringMap.add label index !map
    | _ -> ()) instrs;
  !map

(* A bottom-tested loop laid out as

     h:  ILabel header
         <body>
     l:  branch-nonzero -> header

   qualifies when nothing but [l] mentions the header label, nothing outside
   [h, l] jumps into the middle, and nothing inside jumps to a label above [h].
   That last clause is what keeps a "continue" -- which targets the condition
   block sitting above the body -- from being treated as an ordinary iteration:
   it re-enters the body without passing the bottom test. *)
let contiguous_loops instrs =
  let labels = label_indices instrs in
  let regions = ref [] in
  Array.iteri (fun header instr ->
    match instr with
    | ILabel label ->
      (match label_references instrs label with
       | [latch] when latch > header ->
         (match instrs.(latch) with
          | IBranchNonZero (Temp cond, _) ->
            let inside index = index > header && index <= latch in
            let ok = ref true in
            for index = header + 1 to latch - 1 do
              (match instrs.(index) with
               | ILabel inner ->
                 List.iter
                   (fun reference -> if not (inside reference) then ok := false)
                   (label_references instrs inner)
               | _ -> ());
              match branch_target instrs.(index) with
              | None -> ()
              | Some target ->
                (match StringMap.find_opt target labels with
                 | Some index when index > header -> ()
                 | _ -> ok := false)
            done;
            if !ok then
              regions :=
                { region_start = header; region_stop = latch; region_label = label;
                  region_cond = cond }
                :: !regions
          | _ -> ())
       | _ -> ())
    | _ -> ()) instrs;
  List.rev !regions

let region_has_inner_backedge instrs region =
  let labels = label_indices instrs in
  let found = ref false in
  for index = region.region_start + 1 to region.region_stop - 1 do
    match branch_target instrs.(index) with
    | Some target ->
      (match StringMap.find_opt target labels with
       | Some target_index when target_index <= index -> found := true
       | _ -> ())
    | None -> ()
  done;
  !found

let region_defs instrs region t =
  let acc = ref [] in
  for index = region.region_stop downto region.region_start do
    if instr_dest instrs.(index) = Some t then acc := index :: !acc
  done;
  !acc

let outside_defs instrs region t =
  let acc = ref [] in
  Array.iteri (fun index instr ->
    if (index < region.region_start || index > region.region_stop)
       && instr_dest instr = Some t
    then acc := index :: !acc) instrs;
  !acc

(* The value [t] holds on every entry to the loop, or None when that is not a
   single constant.  Every definition outside the loop has to agree, one of them
   has to dominate the header, and -- the part dominance alone does not give --
   there must be no way back to the header that skips them all.  The back edge
   is excluded from that search: reaching the header along it is the loop, not a
   re-entry. *)
let entry_value instrs (cfg : Cfg.t) doms region t =
  let defs = outside_defs instrs region t in
  let agreed =
    List.fold_left (fun acc index ->
      match acc, instrs.(index) with
      | None, _ -> None
      | Some None, ILoad (_, Imm value) -> Some (Some value)
      | Some (Some previous), ILoad (_, Imm value) when previous = value ->
        Some (Some value)
      | _ -> None) (Some None) defs
  in
  match agreed with
  | Some (Some value)
    when List.exists (fun d -> Cfg.dominates doms d region.region_start) defs ->
    let masked =
      List.fold_left (fun set d -> IntSet.add d set) IntSet.empty defs
    in
    let count = Array.length instrs in
    let seen = Array.make count false in
    let reenters = ref false in
    let rec visit = function
      | [] -> ()
      | index :: rest ->
        if index = region.region_start then begin
          reenters := true;
          visit rest
        end
        else if index < 0 || index >= count || seen.(index) || IntSet.mem index masked
        then visit rest
        else begin
          seen.(index) <- true;
          let succs =
            if index = region.region_stop then
              List.filter (fun s -> s <> region.region_start) cfg.succs.(index)
            else cfg.succs.(index)
          in
          visit (succs @ rest)
        end
    in
    visit cfg.succs.(region.region_start);
    if !reenters then None else Some value
  | _ -> None

(* How many times the body runs.  The loop is bottom-tested, so the answer is
   never zero once control reaches the header.

   The counter must be provably free of overflow.  A closed form is exact modulo
   2^32, but the *number of iterations* is not a modular quantity: a counter
   that wraps past its ceiling runs a different number of times than the
   arithmetic here predicts, so the last value it takes has to stay in range. *)
let trip_count ~init ~step ~op ~bound =
  let continues value =
    match (op : A.bin_op) with
    | A.Lt -> value < bound
    | A.Le -> value <= bound
    | A.Gt -> value > bound
    | A.Ge -> value >= bound
    | A.Ne -> value <> bound
    | _ -> false
  in
  let monotone =
    match (op : A.bin_op) with
    | A.Lt | A.Le -> step > 0
    | A.Gt | A.Ge -> step < 0
    | A.Ne -> step <> 0
    | _ -> false
  in
  if not monotone then None
  else begin
    let ceiling_of_divide distance stride =
      if distance <= 0 then 1 else (distance + stride - 1) / stride
    in
    let count =
      match (op : A.bin_op) with
      | A.Lt -> ceiling_of_divide (bound - init) step
      | A.Le -> ceiling_of_divide (bound + 1 - init) step
      | A.Gt -> ceiling_of_divide (init - bound) (-step)
      | A.Ge -> ceiling_of_divide (init - bound + 1) (-step)
      | A.Ne ->
        let distance = bound - init in
        if distance = 0 || distance mod step <> 0 || distance / step < 1 then 0
        else distance / step
      | _ -> 0
    in
    let count = max count 1 in
    if count > max_i32 then None
    else
      let last = init + (count * step) in
      (* Two independent checks that the answer really is the first exit: the
         loop must stop at [count], and must not have stopped before it. *)
      if last > max_i32 || last < min_i32 then None
      else if continues last then None
      else if count > 1 && not (continues (init + ((count - 1) * step))) then None
      else Some count
  end

(* Everything that is live on some edge leaving the region.  Reading liveness at
   the instruction after the loop is not enough: a "break" leaves from the
   middle, and once redundant jumps have been threaded its target need not be
   the instruction the loop falls through to. *)
let region_exit_live (cfg : Cfg.t) (live : Liveness.t) region =
  let acc = ref IntSet.empty in
  for index = region.region_start to region.region_stop do
    List.iter (fun succ ->
      if succ < region.region_start || succ > region.region_stop then
        acc := IntSet.union !acc live.Liveness.live_in.(succ))
      cfg.succs.(index)
  done;
  !acc

type counted = {
  cr_counter : int;
  cr_init : int;
  cr_step : int;
  cr_trips : int;
  cr_update : int;
  cr_test : int;
}

let counted_region instrs (cfg : Cfg.t) doms region =
  let single_def t =
    match region_defs instrs region t with
    | [definition] -> Some definition
    | _ -> None
  in
  match single_def region.region_cond with
  | None -> None
  | Some test ->
    (match instrs.(test) with
     | IBinOp (_, op, Temp counter, Imm bound) ->
       (* The test has to read the counter after the update, which is the shape
          loop rotation leaves behind. *)
       (match single_def counter with
        | Some update when update < test ->
          (match instrs.(update) with
           | IBinOp (_, A.Add, Temp base, Imm step) when base = counter ->
             (match entry_value instrs cfg doms region counter with
              | None -> None
              | Some init ->
                (match trip_count ~init ~step ~op ~bound with
                 | None -> None
                 | Some trips ->
                   Some
                     { cr_counter = counter; cr_init = init; cr_step = step;
                       cr_trips = trips; cr_update = update; cr_test = test }))
           | _ -> None)
        | _ -> None)
     | _ -> None)

(* =====================================================
   Closed-form loop evaluation

   A loop whose body is straight-line arithmetic computes, for each value it
   carries, a polynomial in the iteration index.  Scalar evolution derives that
   polynomial from the *shape* of the recurrence -- "s grows by i on every
   iteration" is turned into a degree-two chain without the loop being run --
   and the trip count then says where to read it off.

   This is the one place where a loop disappears entirely, so the preconditions
   are deliberately narrow: the body must be pure (no calls, no globals, no
   control flow of its own), so deleting it cannot drop an observable effect;
   every value that outlives the loop must have a closed form, so nothing is
   left undefined; and the derived recurrence is checked against a second
   symbolic pass before anything is rewritten.
   ===================================================== *)

type evolution =
  | Unknown
  | Known of Scev.t

let pure_computation = function
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IShiftRightArith _
  | IShiftRightLogic _ | IMulHigh _ | IBitAnd _ -> true
  | ILoadParam _ | ILoadGlobal _ | IStoreGlobal _ | ICall _ | ILabel _ | IJump _
  | IBranchZero _ | IBranchNonZero _ | IReturn _ -> false

(* One step of symbolic execution.  Addition, subtraction, multiplication and a
   shift by a constant stay inside the polynomial world; everything else only
   folds when its operands have collapsed to constants, which is the same rule
   the rest of the optimizer follows. *)
let evolve value_of instr =
  let operand = function
    | Imm value -> Known (Scev.const value)
    | Temp t -> value_of t
  in
  let lift1 o f =
    match operand o with
    | Known p -> f p
    | Unknown -> Unknown
  in
  let lift2 a b f =
    match operand a, operand b with
    | Known p, Known q -> f p q
    | _ -> Unknown
  in
  let folded1 o f =
    lift1 o (fun p ->
      match Scev.const_value p with
      | Some value -> Known (Scev.const (f value))
      | None -> Unknown)
  in
  let folded2 a b f =
    lift2 a b (fun p q ->
      match Scev.const_value p, Scev.const_value q with
      | Some x, Some y -> (match f x y with Some v -> Known (Scev.const v) | None -> Unknown)
      | _ -> Unknown)
  in
  match instr with
  | ILoad (_, o) -> operand o
  | IUnaryOp (_, A.UPlus, o) -> operand o
  | IUnaryOp (_, A.UMinus, o) -> lift1 o (fun p -> Known (Scev.neg p))
  | IUnaryOp (_, A.Not, o) -> folded1 o (apply_unary A.Not)
  | IBinOp (_, A.Add, a, b) -> lift2 a b (fun p q -> Known (Scev.add p q))
  | IBinOp (_, A.Sub, a, b) -> lift2 a b (fun p q -> Known (Scev.sub p q))
  | IBinOp (_, A.Mul, a, b) ->
    lift2 a b (fun p q ->
      match Scev.mul p q with Some r -> Known r | None -> Unknown)
  | IBinOp (_, op, a, b) -> folded2 a b (apply_binary op)
  | IShiftLeft (_, o, amount) when amount >= 0 && amount < 32 ->
    lift1 o (fun p -> Known (Scev.scale p (1 lsl amount)))
  | IShiftRightArith (_, o, amount) -> folded1 o (fun v -> apply_shift_right_arith v amount)
  | IShiftRightLogic (_, o, amount) -> folded1 o (fun v -> apply_shift_right_logic v amount)
  | IBitAnd (_, o, m) -> folded1 o (fun v -> v land m)
  | IMulHigh (_, a, b) -> folded2 a b (fun x y -> Some (apply_mul_high x y))
  | _ -> Unknown

let closed_form_region instrs (cfg : Cfg.t) doms (live : Liveness.t) region =
  let h = region.region_start and l = region.region_stop in
  let straight_line = ref (l > h + 1) in
  for index = h + 1 to l - 1 do
    if not (pure_computation instrs.(index)) then straight_line := false
  done;
  if not !straight_line then None
  else
    match counted_region instrs cfg doms region with
    | None -> None
    | Some counted ->
      let defined = ref IntSet.empty in
      for index = h + 1 to l - 1 do
        match instr_dest instrs.(index) with
        | Some dst -> defined := IntSet.add dst !defined
        | None -> ()
      done;
      let defined = !defined in
      (* Values that reach the header from a previous iteration are the ones
         that need a recurrence solved; anything else is written before it is
         read and only needs forward evaluation. *)
      let carried = IntSet.inter defined live.Liveness.live_in.(h) in
      let invariants =
        let acc = ref IntMap.empty in
        for index = h + 1 to l - 1 do
          List.iter (fun o ->
            match operand_temp o with
            | Some t when (not (IntSet.mem t defined)) && not (IntMap.mem t !acc) ->
              let value =
                match entry_value instrs cfg doms region t with
                | Some v -> Known (Scev.const v)
                | None -> Unknown
              in
              acc := IntMap.add t value !acc
            | _ -> ()) (instr_operands instrs.(index))
        done;
        !acc
      in
      let resolved = ref IntMap.empty in
      (* One symbolic sweep of the body; returns what was known just before each
         instruction, and what everything evaluates to at the end. *)
      let sweep () =
        let env =
          ref
            (IntSet.fold (fun t acc ->
               IntMap.add t
                 (match IntMap.find_opt t !resolved with
                  | Some p -> Known p
                  | None -> Unknown)
                 acc) defined invariants)
        in
        let before = Hashtbl.create 16 in
        for index = h + 1 to l - 1 do
          Hashtbl.replace before index !env;
          let value =
            evolve
              (fun t -> Option.value (IntMap.find_opt t !env) ~default:Unknown)
              instrs.(index)
          in
          match instr_dest instrs.(index) with
          | Some dst -> env := IntMap.add dst value !env
          | None -> ()
        done;
        (before, !env)
      in
      let progress = ref true in
      while !progress do
        progress := false;
        let before, _ = sweep () in
        IntSet.iter (fun t ->
          if not (IntMap.mem t !resolved) then
            match region_defs instrs region t with
            | [definition] ->
              let env = Hashtbl.find before definition in
              let known = function
                | Imm value -> Some (Scev.const value)
                | Temp u ->
                  (match IntMap.find_opt u env with
                   | Some (Known p) -> Some p
                   | _ -> None)
              in
              let increment =
                match instrs.(definition) with
                | IBinOp (_, A.Add, Temp a, o) when a = t -> known o
                | IBinOp (_, A.Add, o, Temp a) when a = t -> known o
                | IBinOp (_, A.Sub, Temp a, o) when a = t ->
                  Option.map Scev.neg (known o)
                | _ -> None
              in
              (match increment, entry_value instrs cfg doms region t with
               | Some step, Some init ->
                 (match Scev.antidifference init step with
                  | Some closed ->
                    resolved := IntMap.add t closed !resolved;
                    progress := true
                  | None -> ())
               | _ -> ())
            | _ -> ()) carried
      done;
      let _, final = sweep () in
      (* Independent check that each solved recurrence actually reproduces
         itself: the value at the end of iteration n has to be the header value
         at n + 1. *)
      let consistent =
        IntMap.for_all (fun t closed ->
          match IntMap.find_opt t final with
          | Some (Known reached) -> Scev.equal reached (Scev.shift closed)
          | _ -> false) !resolved
      in
      if not consistent then None
      else begin
        let needed = IntSet.inter defined (region_exit_live cfg live region) in
        let last = counted.cr_trips - 1 in
        let replacement =
          IntSet.fold (fun t acc ->
            match acc, IntMap.find_opt t final with
            | None, _ -> None
            | Some instrs_acc, Some (Known closed) ->
              Some (ILoad (t, Imm (Scev.eval closed last)) :: instrs_acc)
            | _ -> None) needed (Some [])
        in
        replacement
      end

let closed_form_loops body =
  let rec attempt body =
    let instrs = Array.of_list body in
    let cfg = Cfg.build body in
    let doms = Cfg.dominators cfg in
    let live = Liveness.analyze cfg in
    let rewritten =
      List.find_map (fun region ->
        match closed_form_region instrs cfg doms live region with
        | Some replacement -> Some (region, replacement)
        | None -> None) (contiguous_loops instrs)
    in
    match rewritten with
    | None -> body
    | Some (region, replacement) ->
      let count = Array.length instrs in
      let before = Array.to_list (Array.sub instrs 0 region.region_start) in
      let after =
        Array.to_list
          (Array.sub instrs (region.region_stop + 1) (count - region.region_stop - 1))
      in
      attempt (before @ replacement @ after)
  in
  attempt body

(* =====================================================
   Counted loop unrolling

   Every iteration of a tight loop pays for the bottom test and the branch back.
   Running the body several times per test amortises that away, and because the
   copies reuse the same temporaries it costs nothing in register pressure --
   the live ranges get longer, but no new values appear.

   The unroll factor has to divide the trip count exactly.  Dropping the
   intermediate tests means the loop can only exit at a multiple of the factor,
   so a factor that does not divide the trip count would overshoot.  Exits from
   inside the body (a "break", a "return") are unaffected: they leave the loop
   early either way.
   ===================================================== *)

let unroll_factors = [8; 4; 2]
let unroll_limit = 96
let unroll_peel_limit = 160

let rename_labels mapping instr =
  let target label = Option.value (StringMap.find_opt label mapping) ~default:label in
  match instr with
  | ILabel label -> ILabel (target label)
  | IJump label -> IJump (target label)
  | IBranchZero (o, label) -> IBranchZero (o, target label)
  | IBranchNonZero (o, label) -> IBranchNonZero (o, target label)
  | other -> other

let unroll_loops body =
  let unrolled = ref StringSet.empty in
  let rec attempt body =
    let instrs = Array.of_list body in
    let cfg = Cfg.build body in
    let doms = Cfg.dominators cfg in
    let live = Liveness.analyze cfg in
    let used = ref (labels_in_body body) in
    let fresh base =
      let rec pick n =
        let candidate = base ^ "_u" ^ string_of_int n in
        if StringSet.mem candidate !used then pick (n + 1)
        else begin
          used := StringSet.add candidate !used;
          candidate
        end
      in
      pick 0
    in
    let plan region =
      if StringSet.mem region.region_label !unrolled then None
      else if region_has_inner_backedge instrs region then None
      else
        match counted_region instrs cfg doms region with
        | None -> None
        | Some counted ->
          let h = region.region_start and l = region.region_stop in
          let size = l - h - 1 in
          (* The factor has to divide the trip count, so whatever it leaves over
             is peeled off in front of the loop.  Peeling is only worth its code
             size when nothing divides exactly, hence the two-stage choice. *)
          let usable factor =
            factor * size <= unroll_limit
            && counted.cr_trips >= factor
            && abs (counted.cr_step * factor) <= max_i32
          in
          let choice =
            match
              List.find_opt
                (fun factor -> usable factor && counted.cr_trips mod factor = 0)
                unroll_factors
            with
            | Some factor -> Some (factor, 0)
            | None ->
              List.find_map (fun factor ->
                let remainder = counted.cr_trips mod factor in
                if usable factor
                   && counted.cr_trips - remainder >= factor
                   && (factor + remainder) * size <= unroll_peel_limit
                then Some (factor, remainder)
                else None) unroll_factors
          in
          if size <= 0 then None
          else
            (match choice with
             | None -> None
             | Some (factor, remainder) ->
               let live_after = region_exit_live cfg live region in
               (* The counter only has to be carried between copies when
                  something other than the update and the test can observe it.
                  When nothing can, the copies drop both and the last one steps
                  by the whole factor at once. *)
               let counter_uses = ref 0 in
               for index = h + 1 to l - 1 do
                 List.iter (fun o ->
                   if o = Temp counted.cr_counter then incr counter_uses)
                   (instr_operands instrs.(index))
               done;
               let fuse =
                 !counter_uses = 2
                 && (not (IntSet.mem counted.cr_counter live_after))
                 && not (IntSet.mem region.region_cond live_after)
               in
               let inner = Array.sub instrs (h + 1) size in
               let copy last =
                 let keep index =
                   last
                   || (not fuse)
                   || (index + h + 1 <> counted.cr_update
                       && index + h + 1 <> counted.cr_test)
                 in
                 let step index instr =
                   if fuse && last && index + h + 1 = counted.cr_update then
                     IBinOp (counted.cr_counter, A.Add, Temp counted.cr_counter,
                             Imm (counted.cr_step * factor))
                   else instr
                 in
                 let selected =
                   Array.to_list (Array.mapi (fun index instr ->
                     if keep index then Some (step index instr) else None) inner)
                   |> List.filter_map Fun.id
                 in
                 if last then selected
                 else begin
                   let mapping =
                     List.fold_left (fun acc instr ->
                       match instr with
                       | ILabel label -> StringMap.add label (fresh label) acc
                       | _ -> acc) StringMap.empty selected
                   in
                   List.map (rename_labels mapping) selected
                 end
               in
               (* The peeled iterations run before the loop is entered, so when
                  the copies have dropped the counter update the peeled ones owe
                  it the distance they covered. *)
               let peeled =
                 List.concat (List.init remainder (fun _ -> copy false))
                 @ (if fuse && remainder > 0 then
                      [IBinOp (counted.cr_counter, A.Add, Temp counted.cr_counter,
                               Imm (counted.cr_step * remainder))]
                    else [])
               in
               let copies =
                 List.concat (List.init (factor - 1) (fun _ -> copy false))
                 @ copy true
               in
               unrolled := StringSet.add region.region_label !unrolled;
               Some
                 (region,
                  peeled
                  @ (ILabel region.region_label :: copies)
                  @ [instrs.(l)]))
    in
    match List.find_map plan (contiguous_loops instrs) with
    | None -> body
    | Some (region, replacement) ->
      let count = Array.length instrs in
      let before = Array.to_list (Array.sub instrs 0 region.region_start) in
      let after =
        Array.to_list
          (Array.sub instrs (region.region_stop + 1) (count - region.region_stop - 1))
      in
      attempt (before @ replacement @ after)
  in
  attempt body

(* =====================================================
   Per-function fixpoint
   ===================================================== *)

let optimize_body body =
  let rec fix body =
    let next =
      body
      |> rewrite_modulo_zero_tests
      |> fold_assignment_temps
      |> local_pass
      (* Before the reciprocal expansion, which would otherwise bury the
         remainder in a multiply sequence this can no longer recognise. *)
      |> strength_reduce_modulo
      (* After local_pass, so a divisor that only became constant through
         propagation is still expanded. *)
      |> expand_constant_division
      |> propagate_constants
      |> cleanup_control_flow
      (* Inside the fixpoint so that collapsing an inner loop can expose the one
         around it, whose body only becomes straight-line once the inner loop is
         gone. *)
      |> closed_form_loops
      |> global_cse
      |> licm
      |> promote_loop_globals
      |> eliminate_dead_defs
      |> eliminate_dead_stores
      |> cleanup_control_flow
    in
    if next = body then body else fix next
  in
  fix body

(* =====================================================
   Loop rotation

   A while loop is lowered top-tested:

     L_cond: <cond>; branch-zero -> L_end; <body>; jump L_cond; L_end:

   which costs an unconditional jump on every iteration.  Rotating it to a
   bottom-tested loop keeps the entry test but replaces the back jump with the
   back branch:

     L_cond: <cond>; branch-zero -> L_end; L_body: <body>; <cond>;
     branch-nonzero -> L_body; L_end:

   The condition is only duplicated when it is pure and re-executable, and the
   number of condition evaluations is unchanged.
   ===================================================== *)

let reexecutable_condition = function
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IShiftRightArith _
  | IShiftRightLogic _ | IMulHigh _ | IBitAnd _ | ILoadGlobal _ -> true
  | ILoadParam _ | IStoreGlobal _ | ICall _ | ILabel _ | IJump _ | IBranchZero _
  | IBranchNonZero _ | IReturn _ -> false

let rotate_loops body =
  let used_labels = ref (labels_in_body body) in
  let rec fresh_label base =
    let candidate = base ^ "_body" in
    if StringSet.mem candidate !used_labels then fresh_label candidate
    else begin
      used_labels := StringSet.add candidate !used_labels;
      candidate
    end
  in
  let split_condition instrs =
    let rec loop acc = function
      | IBranchZero ((Temp _ as condition), end_label) :: rest ->
        Some (List.rev acc, condition, end_label, rest)
      | instr :: rest when reexecutable_condition instr -> loop (instr :: acc) rest
      | _ -> None
    in
    loop [] instrs
  in
  let split_backedge cond_label end_label instrs =
    let rec loop acc = function
      | IJump target :: ILabel label :: rest
        when target = cond_label && label = end_label -> Some (List.rev acc, rest)
      | instr :: rest -> loop (instr :: acc) rest
      | [] -> None
    in
    loop [] instrs
  in
  let rec rotate = function
    | (ILabel cond_label :: rest) as instrs ->
      (match split_condition rest with
       | Some (condition_code, condition, end_label, after_condition) ->
         (match split_backedge cond_label end_label after_condition with
          | Some (loop_body, after_loop) ->
            let body_label = fresh_label cond_label in
            ILabel cond_label
            :: (condition_code
                @ [IBranchZero (condition, end_label); ILabel body_label]
                @ rotate loop_body
                @ condition_code
                @ [IBranchNonZero (condition, body_label); ILabel end_label]
                @ rotate after_loop)
          | None ->
            (match instrs with
             | instr :: rest -> instr :: rotate rest
             | [] -> []))
       | None ->
         (match instrs with
          | instr :: rest -> instr :: rotate rest
          | [] -> []))
    | instr :: rest -> instr :: rotate rest
    | [] -> []
  in
  rotate body

(* =====================================================
   Tail recursion -> loop
   ===================================================== *)

let split_params body =
  let rec loop params = function
    | ILoadParam (dst, index) :: rest -> loop ((index, dst) :: params) rest
    | rest -> (List.sort compare params, rest)
  in
  loop [] body

let rewrite_tail_recursion (func : func_ir) =
  let params, rest = split_params func.body in
  if params = [] then func
  else begin
    let next_temp = ref (max_temp func.body + 1) in
    let fresh () =
      let t = !next_temp in
      incr next_temp;
      t
    in
    let label = Printf.sprintf ".L_%s_tail" func.name in
    let param_dests = List.map snd params in
    (* Arguments are staged through fresh temps first: "f(b, a)" must not write
       the new first parameter before the old one has been read. *)
    let rewrite_call args =
      if List.length args <> List.length param_dests then None
      else
        let staged = List.map (fun operand -> (fresh (), operand)) args in
        Some
          (List.map (fun (t, operand) -> ILoad (t, operand)) staged
           @ List.map2 (fun param (t, _) -> ILoad (param, Temp t)) param_dests staged
           @ [IJump label])
    in
    let rec rewrite acc = function
      | ICall (Some ret, name, args) :: IReturn (Some (Temp result)) :: rest
        when name = func.name && ret = result ->
        (match rewrite_call args with
         | Some instrs -> rewrite (List.rev_append instrs acc) rest
         | None ->
           rewrite
             (IReturn (Some (Temp result)) :: ICall (Some ret, name, args) :: acc)
             rest)
      | ICall (None, name, args) :: IReturn None :: rest when name = func.name ->
        (match rewrite_call args with
         | Some instrs -> rewrite (List.rev_append instrs acc) rest
         | None -> rewrite (IReturn None :: ICall (None, name, args) :: acc) rest)
      | instr :: rest -> rewrite (instr :: acc) rest
      | [] -> List.rev acc
    in
    let rewritten = rewrite [] rest in
    let prologue = List.map (fun (index, dst) -> ILoadParam (dst, index)) params in
    { func with body = prologue @ [ILabel label] @ rewritten }
  end

(* =====================================================
   Inlining
   ===================================================== *)

let inline_cost body =
  List.fold_left (fun cost -> function
    | ILoadParam _ | ILabel _ | IReturn _ -> cost
    | _ -> cost + 1
  ) 0 body

let has_backedge body =
  let cfg = Cfg.build body in
  let doms = Cfg.dominators cfg in
  Cfg.back_edges cfg doms <> []

(* A callee containing a loop is still worth inlining when it is small: the call
   sequence disappears and, more importantly, constant arguments reach into the
   loop body.  The budget is tighter than for straight-line code because the
   body gets duplicated at every call site. *)
let inline_candidate (func : func_ir) =
  func.name <> "main"
  && not (has_call func.body)
  && inline_cost func.body <= (if has_backedge func.body then 20 else 40)

let inline_call next_temp fresh_label (callee : func_ir) dst args =
  let fresh () =
    let t = !next_temp in
    incr next_temp;
    t
  in
  let temp_map =
    List.init (max_temp callee.body + 1) (fun t -> (t, fresh ()))
    |> List.fold_left (fun map (t, mapped) -> IntMap.add t mapped map) IntMap.empty
  in
  let subst_temp t =
    match IntMap.find_opt t temp_map with
    | Some mapped -> mapped
    | None -> failwith "internal error: missing inline register"
  in
  let subst_operand = function
    | Imm _ as imm -> imm
    | Temp t -> Temp (subst_temp t)
  in
  let label_map =
    List.fold_left (fun map -> function
      | ILabel label -> StringMap.add label (fresh_label label) map
      | _ -> map
    ) StringMap.empty callee.body
  in
  let subst_label label =
    match StringMap.find_opt label label_map with
    | Some mapped -> mapped
    | None -> failwith "internal error: missing inline label"
  in
  let continuation = fresh_label (".L_inline_" ^ callee.name) in
  let lower = function
    | ILoadParam (t, index) -> [ILoad (subst_temp t, List.nth args index)]
    | ILabel label -> [ILabel (subst_label label)]
    | IJump label -> [IJump (subst_label label)]
    | IBranchZero (operand, label) ->
      [IBranchZero (subst_operand operand, subst_label label)]
    | IBranchNonZero (operand, label) ->
      [IBranchNonZero (subst_operand operand, subst_label label)]
    | IReturn operand ->
      let result =
        match dst, operand with
        | Some dst, Some operand -> move_or_nop dst (subst_operand operand)
        | Some dst, None -> [ILoad (dst, Imm 0)]
        | None, _ -> []
      in
      result @ [IJump continuation]
    | ICall _ -> failwith "internal error: inline candidate contains a call"
    | instr ->
      let instr = map_operands subst_operand instr in
      [(match instr_dest instr with
        | Some d -> retarget_dest (subst_temp d) instr
        | None -> instr)]
  in
  List.concat_map lower callee.body @ [ILabel continuation]

let inline_func candidates (func : func_ir) =
  let next_temp = ref (max_temp func.body + 1) in
  let used_labels = ref (labels_in_body func.body) in
  let counter = ref 0 in
  let rec fresh_label base =
    let candidate = Printf.sprintf "%s_i%d" base !counter in
    incr counter;
    if StringSet.mem candidate !used_labels then fresh_label base
    else begin
      used_labels := StringSet.add candidate !used_labels;
      candidate
    end
  in
  let rec loop acc = function
    | [] -> List.rev acc
    | ICall (dst, name, args) :: rest when name <> func.name ->
      (match StringMap.find_opt name candidates with
       | Some callee ->
         loop (List.rev_append (inline_call next_temp fresh_label callee dst args) acc) rest
       | None -> loop (ICall (dst, name, args) :: acc) rest)
    | instr :: rest -> loop (instr :: acc) rest
  in
  { func with body = loop [] func.body }

let inline_round funcs =
  let candidates =
    List.fold_left (fun map (func : func_ir) ->
      if inline_candidate func then StringMap.add func.name func map else map
    ) StringMap.empty funcs
  in
  funcs
  |> List.map (inline_func candidates)
  |> List.map (fun func -> { func with body = optimize_body func.body })

let rec inline_fix rounds funcs =
  if rounds = 0 then funcs
  else
    let next = inline_round funcs in
    if next = funcs then funcs else inline_fix (rounds - 1) next

let remove_unreachable_funcs funcs =
  let by_name =
    List.fold_left (fun map (func : func_ir) -> StringMap.add func.name func map)
      StringMap.empty funcs
  in
  let rec visit seen = function
    | [] -> seen
    | name :: rest ->
      if StringSet.mem name seen then visit seen rest
      else
        (match StringMap.find_opt name by_name with
         | None -> visit seen rest
         | Some func ->
           let called =
             List.fold_left (fun calls -> function
               | ICall (_, name, _) -> StringSet.add name calls
               | _ -> calls
             ) StringSet.empty func.body
           in
           visit (StringSet.add name seen) (StringSet.elements called @ rest))
  in
  let reachable = visit StringSet.empty ["main"] in
  List.filter (fun (func : func_ir) -> StringSet.mem func.name reachable) funcs

(* =====================================================
   Materialising loop-invariant immediates

   The backend folds most immediates into the instruction, but some — a modulus,
   a comparison bound that does not fit in 12 bits, a multiplier that is not a
   shift — have to be loaded into a register with [li] first.  Inside a loop
   that [li] runs on every iteration.  Turning such an operand into a temporary
   lets loop-invariant code motion hoist the load into the preheader, where it
   runs once.

   This has to happen after the main fixpoint: constant propagation would
   immediately fold the temporary back into an immediate.
   ===================================================== *)

let is_comparison = function
  | A.Lt | A.Gt | A.Le | A.Ge | A.Eq | A.Ne -> true
  | _ -> false

(* A comparison whose only consumer is a branch is emitted as a conditional
   branch, and those compare two registers.  The immediate forms the backend
   would otherwise use do not apply, so anything but zero costs an [li]. *)
let branch_fused_comparisons (cfg : Cfg.t) =
  let count = Array.length cfg.instrs in
  Array.init count (fun index ->
    match cfg.instrs.(index) with
    | IBinOp (dst, op, _, _) when is_comparison op && index + 1 < count ->
      (match cfg.instrs.(index + 1) with
       | IBranchZero (Temp t, _) | IBranchNonZero (Temp t, _) -> t = dst
       | _ -> false)
    | _ -> false)

let materialize_once body =
  let cfg = Cfg.build body in
  let doms = Cfg.dominators cfg in
  let fused = branch_fused_comparisons cfg in
  let next_temp = ref (max_temp body + 1) in
  let try_loop (header, latch) =
    let nodes = Cfg.natural_loop cfg header latch in
    let wanted = ref [] in
    let temp_for value =
      match List.assoc_opt value !wanted with
      | Some t -> t
      | None ->
        let t = !next_temp in
        incr next_temp;
        wanted := (value, t) :: !wanted;
        t
    in
    let lift ~in_branch op side operand =
      match operand with
      | Imm 0 -> operand
      | Imm value when in_branch || not (Target.immediate_is_free op side value) ->
        Temp (temp_for value)
      | operand -> operand
    in
    let rewritten =
      List.mapi (fun index instr ->
        if not (IntSet.mem index nodes) then instr
        else
          match instr with
          | IBinOp (dst, op, lhs, rhs) ->
            let in_branch = fused.(index) in
            IBinOp
              (dst, op,
               lift ~in_branch op Target.Left lhs,
               lift ~in_branch op Target.Right rhs)
          (* mulh has no immediate form, so the reciprocal always costs an li
             unless it is hoisted. *)
          | IMulHigh (dst, lhs, rhs) ->
            IMulHigh
              (dst,
               lift ~in_branch:true A.Mul Target.Left lhs,
               lift ~in_branch:true A.Mul Target.Right rhs)
          | instr -> instr
      ) body
    in
    if !wanted = [] then None
    else
      let loads =
        !wanted
        |> List.rev
        |> List.map (fun (value, t) -> ILoad (t, Imm value))
      in
      Some
        (rewritten
         |> List.mapi (fun index instr ->
           if index = header then loads @ [instr] else [instr])
         |> List.concat)
  in
  match List.find_map try_loop (Cfg.back_edges cfg doms) with
  | Some body -> body
  | None -> body

let materialize_loop_constants body =
  let rec fix body =
    let next = materialize_once body in
    if next = body then body else fix next
  in
  fix body

(* =====================================================
   Splitting a parameter's live range

   Consider a function that answers a cheap case up front and only then does
   real work:

     int fib(int n) { if (n < 2) return n; return fib(n-1) + fib(n-2); }

   [n] is read on the early-exit path and again after two calls, so its live
   range crosses a call and the allocator has to give it a callee-saved
   register.  That decision reaches backwards: the incoming argument must be
   copied into that register at entry, and the register has to be saved and
   restored, all of which the early exit pays for and none of which it needs.

   Copying [n] once at the head of the region that contains the calls splits
   the range in two.  The entry half never crosses a call, so it can stay in
   the argument register it arrived in, and the early exit becomes free.  The
   copy is not new work: it replaces the entry copy that was there before, and
   only runs on the path that was going to pay for it anyway.

   This runs last, after the main fixpoint, because copy propagation would
   otherwise fold the split straight back together.
   ===================================================== *)

let split_once body =
  let cfg = Cfg.build body in
  let count = Array.length cfg.instrs in
  let doms = Cfg.dominators cfg in
  let liveness = Liveness.analyze cfg in
  let depths = Cfg.loop_depths cfg in
  let counts = definition_counts body in
  let indices = List.init count (fun i -> i) in
  let param_temps =
    Array.to_list cfg.instrs
    |> List.filter_map (function ILoadParam (t, _) -> Some t | _ -> None)
  in
  let definition_index t =
    List.find_opt (fun i -> instr_dest cfg.instrs.(i) = Some t) indices
  in
  let crosses_call_at i t =
    match cfg.instrs.(i) with
    | ICall _ ->
      IntSet.mem t liveness.Liveness.live_out.(i) && not (IntSet.mem t cfg.defs.(i))
    | _ -> false
  in
  let try_label j =
    (* A split point has to run at most once per call, so never inside a loop. *)
    if depths.(j) > 0 then None
    else
      match cfg.instrs.(j) with
      | ILabel _ ->
        let in_region = Array.init count (fun i -> Cfg.dominates doms j i) in
        let worth_splitting t =
          IntMap.find_opt t counts = Some 1
          && (match definition_index t with
              | Some d -> not in_region.(d)
              | None -> false)
          && IntSet.mem t liveness.Liveness.live_in.(j)
          && List.exists (fun i -> in_region.(i) && crosses_call_at i t) indices
          (* Splitting only pays if the remaining range is call-free. *)
          && not (List.exists (fun i -> (not in_region.(i)) && crosses_call_at i t) indices)
        in
        (match List.filter worth_splitting param_temps with
         | [] -> None
         | temps -> Some (j, in_region, temps))
      | _ -> None
  in
  match List.find_map try_label indices with
  | None -> body
  | Some (j, in_region, temps) ->
    let next_temp = ref (max_temp body + 1) in
    let renaming =
      List.map (fun t ->
        let fresh = !next_temp in
        incr next_temp;
        (t, fresh)
      ) temps
    in
    let copies = List.map (fun (t, fresh) -> ILoad (fresh, Temp t)) renaming in
    let rename = function
      | Temp t as operand ->
        (match List.assoc_opt t renaming with Some fresh -> Temp fresh | None -> operand)
      | operand -> operand
    in
    body
    |> List.mapi (fun i instr ->
      if i = j then instr :: copies
      else if in_region.(i) then [map_operands rename instr]
      else [instr])
    |> List.concat

let split_param_live_ranges body =
  let rec fix body =
    let next = split_once body in
    if next = body then body else fix next
  in
  fix body

(* =====================================================
   Entry point
   ===================================================== *)

let optimize_func func =
  let func = rewrite_tail_recursion func in
  { func with body = optimize_body (rotate_loops func.body) }

let run (program : program) : program =
  let funcs =
    program.funcs
    |> List.map optimize_func
    |> inline_fix 4
    |> remove_unreachable_funcs
    |> List.map (fun func ->
      let body =
        func.body
        (* Unrolling runs once, after the fixpoint has finished shrinking the
           body -- the decision to unroll depends on how big that body ended up,
           and re-running the fixpoint afterwards is what removes the now-dead
           copies of the loop test. *)
        |> unroll_loops
        |> optimize_body
        |> materialize_loop_constants
        |> licm
        |> eliminate_dead_defs
        |> cleanup_control_flow
        |> split_param_live_ranges
      in
      { func with body; temp_count = max_temp body + 1 })
  in
  { program with funcs }
