(** Optimization passes: copy propagation and dead code elimination *)

open Ir

(* ------------------------------------------------------------------ *)
(*  Helper: split instructions into basic blocks.
    A block starts at a label or after a jump, and ends at a jump.
*)
type bb = instr list

let split_blocks (body : instr list) : bb list =
  let rec go cur acc = function
    | [] ->
      if cur = [] then acc else List.rev ((List.rev cur) :: acc)
    | (ILabel _ as i) :: rest ->
      let acc' = if cur = [] then acc else (List.rev cur) :: acc in
      go [i] acc' rest
    | (IJump _ as i) :: rest ->
      let block = List.rev (i :: cur) in
      go [] (block :: acc) rest
    | i :: rest ->
      go (i :: cur) acc rest
  in
  List.rev (go [] [] body)

(* ------------------------------------------------------------------ *)
(*  1. Copy propagation within a single basic block.                  *)
(*     Eliminates ILoad(d, Temp s) by replacing all uses of d with s  *)
(*     as long as s is not redefined later in the block.              *)
(* ------------------------------------------------------------------ *)
let copy_prop_block (instrs : instr list) : instr list =
  let copy_map = Hashtbl.create 16 in

  let rec resolve_temp t =
    match Hashtbl.find_opt copy_map t with
    | Some s -> resolve_temp s
    | None -> t
  in

  let resolve_operand = function
    | Temp t -> Temp (resolve_temp t)
    | op -> op
  in

  let apply_resolve instr =
    match instr with
    | ILoad (d, op) -> ILoad (d, resolve_operand op)
    | ILoadGlobal (d, g) -> ILoadGlobal (d, g)
    | IStoreGlobal (g, t) -> IStoreGlobal (g, resolve_temp t)
    | IBinOp (d, op, a, b) -> IBinOp (d, op, resolve_temp a, resolve_temp b)
    | IUnaryOp (d, op, s) -> IUnaryOp (d, op, resolve_temp s)
    | ICall (d, name, args) -> ICall (d, name, List.map resolve_temp args)
    | ICallVoid (name, args) -> ICallVoid (name, List.map resolve_temp args)
    | IBranchTrue (t, l) -> IBranchTrue (resolve_temp t, l)
    | IBranchFalse (t, l) -> IBranchFalse (resolve_temp t, l)
    | IReturn (Some t) -> IReturn (Some (resolve_temp t))
    | i -> i
  in

  let kill_value t =
    let to_remove = Hashtbl.fold (fun k v acc ->
      if v = t then k :: acc else acc
    ) copy_map [] in
    List.iter (Hashtbl.remove copy_map) to_remove
  in

  let dest_temp = function
    | ILoad (d,_) | ILoadGlobal (d,_) | IBinOp (d,_,_,_)
    | IUnaryOp (d,_,_) | ICall (d,_,_) -> Some d
    | _ -> None
  in

  let rec go acc = function
    | [] -> List.rev acc
    | instr :: rest ->
      let instr = apply_resolve instr in
      (match instr with
       | ILoad (d, Temp s) when d <> s ->
         Hashtbl.remove copy_map d;
         Hashtbl.add copy_map d s;
         go acc rest
       | _ ->
         (match dest_temp instr with
          | Some d ->
            Hashtbl.remove copy_map d;
            kill_value d
          | None -> ());
         go (instr :: acc) rest)
  in
  go [] instrs

let copy_propagation func =
  let blocks = split_blocks func.body in
  let new_body = List.concat_map copy_prop_block blocks in
  { func with body = new_body }

(* ------------------------------------------------------------------ *)
(*  2. Dead code elimination (backward liveness).                     *)
(*     Removes pure instructions whose result is never used.          *)
(* ------------------------------------------------------------------ *)
let dce_function func =
  let used = Hashtbl.create (List.length func.body * 2) in

  let mark t = Hashtbl.replace used t () in

  let uses_of = function
    | ILoad (_, Temp s) -> [s]
    | IStoreGlobal (_, t) -> [t]
    | IBinOp (_, _, a, b) -> [a; b]
    | IUnaryOp (_, _, s) -> [s]
    | ICall (_, _, args) | ICallVoid (_, args) -> args
    | IBranchTrue (t, _) | IBranchFalse (t, _) -> [t]
    | IReturn (Some t) -> [t]
    | _ -> []
  in

  let is_pure = function
    | ILoad _ | ILoadGlobal _ | IBinOp _ | IUnaryOp _ -> true
    | _ -> false
  in

  let dest_temp = function
    | ILoad (d,_) | ILoadGlobal (d,_) | IBinOp (d,_,_,_)
    | IUnaryOp (d,_,_) | ICall (d,_,_) -> Some d
    | _ -> None
  in

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun i ->
      List.iter (fun t ->
        if not (Hashtbl.mem used t) then begin
          mark t; changed := true
        end
      ) (uses_of i)
    ) func.body
  done;

  let new_body = List.filter (fun i ->
    match dest_temp i with
    | Some d when is_pure i && not (Hashtbl.mem used d) -> false
    | _ -> true
  ) func.body in
  { func with body = new_body }

(* ------------------------------------------------------------------ *)
(*  Combine passes: copy propagation then DCE                         *)
(* ------------------------------------------------------------------ *)
let run (prog : program) : program =
  let funcs = List.map (fun f ->
    let f1 = copy_propagation f in
    let f2 = dce_function f1 in
    f2
  ) prog.funcs in
  { prog with funcs }