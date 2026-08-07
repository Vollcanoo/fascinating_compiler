(** Graph-colouring register allocation over the instruction-level CFG.

    Three things decide where a value lives:

    - Interference: two values that are live at the same time cannot share a
      register.  Edges come from liveness, so a value that stays live across a
      loop back edge keeps its register for the whole loop.
    - Register class: a0-a7 and t3-t5 are caller-saved.  A leaf function may use
      all of them for free; a function that calls out may only put values there
      when they are not live across a call, and never uses a0-a7 (those are
      being loaded with outgoing arguments).
    - Cost: nodes are coloured in order of a loop-depth weighted use count, so
      an inner-loop value is coloured before, and therefore spilled after, a
      value that is only touched once at the top level.

    Move, parameter and return-value preferences are honoured when the preferred
    register is free, which is what removes most of the [mv] traffic. *)

open Ir

module IntMap = Map.Make (Int)
module IntSet = Cfg.IntSet
module StringSet = Set.Make (String)

type location =
  | Reg of string
  | Spill of int

type allocation = {
  locations : location IntMap.t;
  spill_slots : int;
  (* Callee-saved registers this function actually used, so the prologue only
     saves what it has to. *)
  used_regs : string list;
}

let callee_saved =
  ["s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"]

let arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |]

(* t0/t1/t2 are the code generator's scratch registers and t6 is reserved for
   large-offset address arithmetic, so only t3-t5 are allocatable. *)
let scratch_regs = ["t3"; "t4"; "t5"]

let arg_index phys =
  let rec loop i =
    if i >= Array.length arg_regs then None
    else if arg_regs.(i) = phys then Some i
    else loop (i + 1)
  in
  loop 0

let is_caller_saved phys = List.mem phys scratch_regs || arg_index phys <> None

let allocatable_regs = scratch_regs @ Array.to_list arg_regs @ callee_saved

(* An argument register is loaded at a call site in index order, so a value may
   only live in one when every call passes it in that exact position.  A value
   passed on the stack (index 8 and up) is read after a0-a7 have already been
   overwritten, so it may not live in one at all. *)
type arg_constraint =
  | Only of int
  | Forbidden

let arg_constraints body =
  let record map t position =
    let value =
      match IntMap.find_opt t map with
      | None -> if position < Array.length arg_regs then Only position else Forbidden
      | Some (Only existing) when existing = position -> Only position
      | Some _ -> Forbidden
    in
    IntMap.add t value map
  in
  List.fold_left (fun map -> function
    | ICall (_, _, args) ->
      List.fold_left (fun (map, position) operand ->
        let map =
          match operand with Temp t -> record map t position | Imm _ -> map
        in
        (map, position + 1)
      ) (map, 0) args
      |> fst
    | _ -> map
  ) IntMap.empty body

(* Incoming arguments sit in a0-a7 until the prologue copies them out.  As long
   as every ILoadParam is part of the leading run of the body, no other value is
   defined before that has happened, and the argument registers are free for
   anything else afterwards. *)
let prologue_is_leading body =
  let rec skip = function
    | ILoadParam _ :: rest -> skip rest
    | rest -> rest
  in
  not (List.exists (function ILoadParam _ -> true | _ -> false) (skip body))

let location allocation t =
  match IntMap.find_opt t allocation.locations with
  | Some location -> location
  | None -> Spill 0

(* =====================================================
   Interference graph
   ===================================================== *)

let add_node graph t = if IntMap.mem t graph then graph else IntMap.add t IntSet.empty graph

let add_edge graph a b =
  if a = b then graph
  else
    let graph = add_node (add_node graph a) b in
    graph
    |> IntMap.add a (IntSet.add b (IntMap.find a graph))
    |> IntMap.add b (IntSet.add a (IntMap.find b graph))

let build_graph (cfg : Cfg.t) (liveness : Liveness.t) body =
  let graph = ref IntMap.empty in
  for t = 0 to max_temp body do
    graph := add_node !graph t
  done;
  Array.iteri (fun index defs ->
    (* A register copy does not make its two ends conflict: right after
       "dst = src" both hold the same value, so giving them one register just
       turns the copy into a no-op.  Counting the copy itself as interference
       is what would keep an induction variable and its incremented value in
       separate registers, leaving a mv in the loop forever.  If they ever stop
       agreeing, the redefinition adds the edge at that point. *)
    let copy_source =
      match cfg.instrs.(index) with
      | ILoad (_, Temp src) -> Some src
      | _ -> None
    in
    IntSet.iter (fun def ->
      IntSet.iter (fun live ->
        if Some live <> copy_source then graph := add_edge !graph def live
      ) liveness.Liveness.live_out.(index)
    ) defs
  ) cfg.defs;
  (* Every incoming argument is copied to its home at entry, including arguments
     that are never read.  Those copies must not overwrite one another, so the
     parameter temporaries form a clique regardless of liveness. *)
  let param_temps =
    Array.to_list cfg.instrs
    |> List.filter_map (function ILoadParam (dst, _) -> Some dst | _ -> None)
  in
  List.iter (fun a -> List.iter (fun b -> graph := add_edge !graph a b) param_temps)
    param_temps;
  !graph

(* =====================================================
   Preferences and costs
   ===================================================== *)

let param_preferences body =
  List.fold_left (fun prefs -> function
    | ILoadParam (dst, index) when index < Array.length arg_regs ->
      IntMap.add dst arg_regs.(index) prefs
    | _ -> prefs
  ) IntMap.empty body

(* Every place the ABI already dictates a register: incoming parameters, the
   return value, outgoing arguments and call results.  Honouring these is what
   removes the shuffling around calls. *)
let physical_preferences body =
  let add t phys prefs =
    let existing = IntMap.find_opt t prefs |> Option.value ~default:[] in
    if List.mem phys existing then prefs else IntMap.add t (existing @ [phys]) prefs
  in
  List.fold_left (fun prefs -> function
    | ILoadParam (dst, index) when index < Array.length arg_regs ->
      add dst arg_regs.(index) prefs
    | IReturn (Some (Temp t)) -> add t "a0" prefs
    | ICall (dst, _, args) ->
      let prefs = match dst with Some d -> add d "a0" prefs | None -> prefs in
      List.fold_left (fun (prefs, position) operand ->
        let prefs =
          match operand with
          | Temp t when position < Array.length arg_regs ->
            add t arg_regs.(position) prefs
          | _ -> prefs
        in
        (prefs, position + 1)
      ) (prefs, 0) args
      |> fst
    | _ -> prefs
  ) IntMap.empty body

let move_preferences body =
  let add a b prefs =
    if a = b then prefs
    else
      let existing = IntMap.find_opt a prefs |> Option.value ~default:[] in
      IntMap.add a (b :: existing) prefs
  in
  List.fold_left (fun prefs -> function
    | ILoad (dst, Temp src) -> prefs |> add dst src |> add src dst
    | _ -> prefs
  ) IntMap.empty body

let temp_weights (cfg : Cfg.t) =
  let depths = Cfg.loop_depths cfg in
  let weights = ref IntMap.empty in
  Array.iteri (fun index _ ->
    let amount = 1 + (10 * depths.(index)) in
    IntSet.union cfg.uses.(index) cfg.defs.(index)
    |> IntSet.iter (fun t ->
      let current = IntMap.find_opt t !weights |> Option.value ~default:0 in
      weights := IntMap.add t (current + amount) !weights)
  ) cfg.instrs;
  !weights

let regs_live_across_calls (cfg : Cfg.t) (liveness : Liveness.t) =
  let across = ref IntSet.empty in
  Array.iteri (fun index instr ->
    match instr with
    | ICall _ ->
      across :=
        IntSet.union !across
          (IntSet.diff liveness.Liveness.live_out.(index) cfg.defs.(index))
    | _ -> ()
  ) cfg.instrs;
  !across

(* =====================================================
   Colouring
   ===================================================== *)

let allocate (func : func_ir) : allocation =
  let body = func.body in
  let cfg = Cfg.build body in
  let liveness = Liveness.analyze cfg in
  let graph = build_graph cfg liveness body in
  let regs = allocatable_regs in
  let param_count = min (List.length func.params) (Array.length arg_regs) in
  let param_prefs = param_preferences body in
  let physical_prefs = physical_preferences body in
  let move_prefs = move_preferences body in
  let arg_cons = arg_constraints body in
  let leading_prologue = prologue_is_leading body in
  let call_live = regs_live_across_calls cfg liveness in
  let weights = temp_weights cfg in
  let weight t = IntMap.find_opt t weights |> Option.value ~default:0 in
  let usable t phys =
    (* Caller-saved registers do not survive a call. *)
    (not (is_caller_saved phys) || not (IntSet.mem t call_live))
    && (match arg_index phys with
        | None -> true
        | Some index ->
          (match IntMap.find_opt t param_prefs with
           | Some preferred -> preferred = phys
           | None -> leading_prologue || index >= param_count)
          && (match IntMap.find_opt t arg_cons with
              | None -> true
              | Some (Only position) -> position = index
              | Some Forbidden -> false))
  in
  let nodes =
    IntMap.bindings graph
    |> List.sort (fun (a, a_neighbors) (b, b_neighbors) ->
      let by_weight = compare (weight b) (weight a) in
      if by_weight <> 0 then by_weight
      else compare (IntSet.cardinal b_neighbors) (IntSet.cardinal a_neighbors))
  in
  let locations, used_phys, spill_slots =
    List.fold_left (fun (locations, used_phys, next_slot) (t, neighbors) ->
      let taken =
        IntSet.fold (fun neighbor taken ->
          match IntMap.find_opt neighbor locations with
          | Some (Reg phys) -> StringSet.add phys taken
          | _ -> taken
        ) neighbors StringSet.empty
      in
      let available phys =
        List.mem phys regs && usable t phys && not (StringSet.mem phys taken)
      in
      let preferred =
        let candidates =
          (IntMap.find_opt t physical_prefs |> Option.value ~default:[])
          @ (IntMap.find_opt t move_prefs
             |> Option.value ~default:[]
             |> List.filter_map (fun other ->
               match IntMap.find_opt other locations with
               | Some (Reg phys) -> Some phys
               | _ -> None))
        in
        List.find_opt available candidates
      in
      match (match preferred with Some _ as p -> p | None -> List.find_opt available regs) with
      | Some phys ->
        (IntMap.add t (Reg phys) locations, StringSet.add phys used_phys, next_slot)
      | None -> (IntMap.add t (Spill next_slot) locations, used_phys, next_slot + 1)
    ) (IntMap.empty, StringSet.empty, 0) nodes
  in
  let used_regs = List.filter (fun reg -> StringSet.mem reg used_phys) callee_saved in
  { locations; spill_slots; used_regs }
