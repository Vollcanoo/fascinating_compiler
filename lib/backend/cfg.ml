(** Instruction-level control flow graph.

    Every IR instruction is a node.  That is finer-grained than a basic-block
    graph, but it keeps the data-flow passes (constant propagation, available
    expressions, liveness) and the register allocator on one shared structure,
    and it removes the need to split and re-stitch blocks around every rewrite. *)

open Ir

module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)

type t = {
  instrs : instr array;
  succs : int list array;
  preds : int list array;
  uses : IntSet.t array;
  defs : IntSet.t array;
}

let operand_uses = function
  | Imm _ -> IntSet.empty
  | Temp t -> IntSet.singleton t

let instr_uses_defs instr =
  let uses =
    List.fold_left
      (fun set operand -> IntSet.union set (operand_uses operand))
      IntSet.empty (instr_operands instr)
  in
  let defs =
    match instr_dest instr with
    | Some dst -> IntSet.singleton dst
    | None -> IntSet.empty
  in
  (uses, defs)

let build_label_map instrs =
  let map = ref StringMap.empty in
  Array.iteri (fun index instr ->
    match instr with
    | ILabel label -> map := StringMap.add label index !map
    | _ -> ()
  ) instrs;
  !map

let lookup_label label_map label =
  match StringMap.find_opt label label_map with
  | Some index -> index
  | None -> failwith ("internal error: jump to unknown label " ^ label)

let successors label_map count index instr =
  let next = if index + 1 < count then [index + 1] else [] in
  match instr with
  | IJump label -> [lookup_label label_map label]
  | IBranchZero (_, label) | IBranchNonZero (_, label) ->
    lookup_label label_map label :: next
  | IReturn _ -> []
  | _ -> next

let build_preds succs =
  let preds = Array.make (Array.length succs) [] in
  Array.iteri (fun index succ_list ->
    List.iter (fun succ -> preds.(succ) <- index :: preds.(succ)) succ_list
  ) succs;
  preds

let build (body : instr list) : t =
  let instrs = Array.of_list body in
  let count = Array.length instrs in
  let label_map = build_label_map instrs in
  let succs = Array.mapi (successors label_map count) instrs in
  let preds = build_preds succs in
  let uses_defs = Array.map instr_uses_defs instrs in
  {
    instrs;
    succs;
    preds;
    uses = Array.map fst uses_defs;
    defs = Array.map snd uses_defs;
  }

(* =====================================================
   Reachability
   ===================================================== *)

let reachable (cfg : t) =
  let count = Array.length cfg.instrs in
  let seen = Array.make count false in
  let rec visit = function
    | [] -> ()
    | index :: rest ->
      if index < 0 || index >= count || seen.(index) then visit rest
      else begin
        seen.(index) <- true;
        visit (cfg.succs.(index) @ rest)
      end
  in
  if count > 0 then visit [0];
  seen

(* =====================================================
   Dominators and natural loops
   ===================================================== *)

let all_indices count =
  let rec loop i set = if i < 0 then set else loop (i - 1) (IntSet.add i set) in
  loop (count - 1) IntSet.empty

let intersect_sets = function
  | [] -> IntSet.empty
  | first :: rest -> List.fold_left IntSet.inter first rest

let dominators (cfg : t) =
  let count = Array.length cfg.instrs in
  let doms = Array.make count IntSet.empty in
  if count > 0 then begin
    let all = all_indices count in
    for index = 0 to count - 1 do
      doms.(index) <- (if index = 0 then IntSet.singleton 0 else all)
    done;
    let changed = ref true in
    while !changed do
      changed := false;
      for index = 1 to count - 1 do
        let pred_doms = List.map (fun pred -> doms.(pred)) cfg.preds.(index) in
        let next = IntSet.add index (intersect_sets pred_doms) in
        if not (IntSet.equal next doms.(index)) then begin
          doms.(index) <- next;
          changed := true
        end
      done
    done
  end;
  doms

let dominates doms dominator node = IntSet.mem dominator doms.(node)

(* The natural loop of a back edge latch -> header is the header plus every
   node that can reach the latch without going through the header. *)
let natural_loop (cfg : t) header latch =
  let rec visit seen = function
    | [] -> seen
    | node :: rest ->
      if IntSet.mem node seen then visit seen rest
      else visit (IntSet.add node seen) (cfg.preds.(node) @ rest)
  in
  visit (IntSet.singleton header) [latch]

let back_edges (cfg : t) doms =
  let count = Array.length cfg.instrs in
  let edges = ref [] in
  for index = count - 1 downto 0 do
    List.iter (fun succ ->
      if dominates doms succ index then edges := (succ, index) :: !edges
    ) cfg.succs.(index)
  done;
  !edges

(* How many loops each instruction sits inside; used to weight spill decisions
   so that a value used in an inner loop keeps its register. *)
let loop_depths (cfg : t) =
  let count = Array.length cfg.instrs in
  let depths = Array.make count 0 in
  let doms = dominators cfg in
  List.iter (fun (header, latch) ->
    natural_loop cfg header latch
    |> IntSet.iter (fun node -> depths.(node) <- depths.(node) + 1)
  ) (back_edges cfg doms);
  depths
