(** Optimization pipeline for the ToyC IR.

    Everything here is a static program transformation driven by the AST, the
    IR and control/data-flow facts.  Constants are only evaluated when every
    operand has been *proven* constant; calls, loops and side effecting
    operations are never executed at compile time, so [-opt] cannot degenerate
    into "precompute main and return a literal".

    Pass order (per function, run to a fixpoint):

      fold_assignment_temps  collapse "t = expr; x = t" into "x = expr"
      local_pass             constant/copy propagation, algebraic simplification,
                             strength reduction and local CSE
      propagate_constants    CFG-wide constant propagation with reachability
      cleanup_control_flow   redundant jumps, unreachable code, unused labels
      global_cse             available expressions across blocks
      licm                   loop-invariant code motion
      eliminate_dead_defs    liveness-driven dead definition removal
      eliminate_dead_stores  redundant global stores
      cleanup_control_flow

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
  | IBitAnd (_, operand, mask) -> Some (EBitAnd (operand, mask))
  | _ -> None

let expr_of_instrs = function
  | [instr] -> expr_of_instr instr
  | _ -> None

let expr_temps = function
  | EUnary (_, operand) | EShift (operand, _) | EBitAnd (operand, _) ->
    (match operand_temp operand with Some t -> IntSet.singleton t | None -> IntSet.empty)
  | EBinary (_, lhs, rhs) ->
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
  | IBitAnd (_, operand, mask) -> IBitAnd (dst, operand, mask)
  | ILoadGlobal (_, name) -> ILoadGlobal (dst, name)
  | ICall (Some _, name, args) -> ICall (Some dst, name, args)
  | instr -> instr

let retargetable = function
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IBitAnd _ | ILoadGlobal _
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
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IBitAnd _ -> true
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
   Per-function fixpoint
   ===================================================== *)

let optimize_body body =
  let rec fix body =
    let next =
      body
      |> rewrite_modulo_zero_tests
      |> fold_assignment_temps
      |> local_pass
      |> propagate_constants
      |> cleanup_control_flow
      |> global_cse
      |> licm
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
  | ILoad _ | IUnaryOp _ | IBinOp _ | IShiftLeft _ | IBitAnd _ | ILoadGlobal _ -> true
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
        match instr with
        | IBinOp (dst, op, lhs, rhs) when IntSet.mem index nodes ->
          let in_branch = fused.(index) in
          IBinOp
            (dst, op,
             lift ~in_branch op Target.Left lhs,
             lift ~in_branch op Target.Right rhs)
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
        |> materialize_loop_constants
        |> licm
        |> eliminate_dead_defs
        |> cleanup_control_flow
        |> split_param_live_ranges
      in
      { func with body; temp_count = max_temp body + 1 })
  in
  { program with funcs }
