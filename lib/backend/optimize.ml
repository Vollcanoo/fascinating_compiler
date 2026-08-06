(** Optimization passes for ToyC IR *)

open Ir
open Cfg
module A = Ast



(* =====================================================
   Constant evaluation
   ===================================================== *)

let eval_binop (op:A.bin_op) a b =
  match op with

  | A.Add -> Some (a+b)
  | A.Sub -> Some (a-b)
  | A.Mul -> Some (a*b)

  | A.Div ->
      if b=0 then None
      else if a=min_int && b=(-1)
      then None
      else Some(a/b)

  | A.Mod ->
      if b=0 then None
      else Some(a mod b)

  | A.Lt ->
      Some(if a<b then 1 else 0)

  | A.Gt ->
      Some(if a>b then 1 else 0)

  | A.Le ->
      Some(if a<=b then 1 else 0)

  | A.Ge ->
      Some(if a>=b then 1 else 0)

  | A.Eq ->
      Some(if a=b then 1 else 0)

  | A.Ne ->
      Some(if a<>b then 1 else 0)

  | A.And ->
      Some(if a<>0 && b<>0 then 1 else 0)

  | A.Or ->
      Some(if a<>0 || b<>0 then 1 else 0)



let eval_unary (op:A.unary_op) a =
  match op with

  | A.UPlus ->
      Some a

  | A.UMinus ->
      if a=min_int then None
      else Some(-a)

  | A.Not ->
      Some(if a=0 then 1 else 0)



(* =====================================================
   Optimization environment
   ===================================================== *)


(* common-subexpression keys: commutative ops are normalized so
   `a+b` and `b+a` hash to the same entry *)

let is_commutative = function
  | A.Add | A.Mul | A.And | A.Or | A.Eq | A.Ne -> true
  | A.Sub | A.Div | A.Mod | A.Lt | A.Gt | A.Le | A.Ge -> false

let bin_key (op:A.bin_op) a b =
  if is_commutative op && b < a then (op, b, a) else (op, a, b)

type env =
{
  const_table:(int,int) Hashtbl.t;

  copy_table:(int,int) Hashtbl.t;

  expr_table:(A.bin_op*int*int,int) Hashtbl.t;

  unary_table:(A.unary_op*int,int) Hashtbl.t;
}



let create_env () =
{
 const_table=Hashtbl.create 64;
 copy_table=Hashtbl.create 64;
 expr_table=Hashtbl.create 64;
 unary_table=Hashtbl.create 64;
}



let clear_env env =
(
 Hashtbl.clear env.const_table;
 Hashtbl.clear env.copy_table;
 Hashtbl.clear env.expr_table;
 Hashtbl.clear env.unary_table
)



(* remove definitions of t *)

let kill env t =

 Hashtbl.remove env.const_table t;

 Hashtbl.remove env.copy_table t;



 let dead = ref [] in

 Hashtbl.iter
   (fun k v ->
      if v=t then
        dead:=k::!dead)
   env.copy_table;


 List.iter
   (fun k ->
      Hashtbl.remove env.copy_table k)
   !dead;



 (* any cached expression that reads or produced t is now stale *)

 let dead_expr = ref [] in

 Hashtbl.iter
   (fun (op,a,b) v ->
      if a=t || b=t || v=t then
        dead_expr:=(op,a,b)::!dead_expr)
   env.expr_table;

 List.iter
   (fun k -> Hashtbl.remove env.expr_table k)
   !dead_expr;


 let dead_unary = ref [] in

 Hashtbl.iter
   (fun (op,a) v ->
      if a=t || v=t then
        dead_unary:=(op,a)::!dead_unary)
   env.unary_table;

 List.iter
   (fun k -> Hashtbl.remove env.unary_table k)
   !dead_unary



(* resolve copy chain *)

let rec resolve_copy env t =

 match Hashtbl.find_opt env.copy_table t with

 | None ->
     t

 | Some x ->

     if x=t then t

     else

       let r =
         resolve_copy env x
       in

       Hashtbl.replace env.copy_table t r;

       r



let get_const env t =

 let t =
   resolve_copy env t
 in

 Hashtbl.find_opt env.const_table t



(* =====================================================
   Algebraic identities

   Cases where one operand alone settles the result, so the
   operation is replaced by a copy of the other side or by a
   constant, even though that other side is unknown. Operands are
   temps and reading one has no side effect, so dropping a side is
   always safe.

   Division and modulo by zero are left alone: folding them would
   invent a result for something the target would trap on.
   ===================================================== *)

let simplify_algebraic (op:A.bin_op) ca cb a b =
  match op, ca, cb with

  | A.Add, Some 0, _ -> `Copy b
  | A.Add, _, Some 0 -> `Copy a

  | A.Sub, _, Some 0 -> `Copy a
  | A.Sub, _, _ when a = b -> `Const 0

  | A.Mul, Some 1, _ -> `Copy b
  | A.Mul, _, Some 1 -> `Copy a
  | A.Mul, Some 0, _ -> `Const 0
  | A.Mul, _, Some 0 -> `Const 0

  | A.Div, _, Some 1 -> `Copy a
  | A.Mod, _, Some 1 -> `Const 0

  (* a relation between a value and itself needs no comparison *)
  | (A.Eq | A.Le | A.Ge), _, _ when a = b -> `Const 1
  | (A.Ne | A.Lt | A.Gt), _, _ when a = b -> `Const 0

  | _ -> `Keep



(* =====================================================
   Rewrite instruction
   ===================================================== *)

let optimize_instr env instr =


match instr with



(* t = immediate *)

| ILoad(dst,Imm n) ->


    kill env dst;

    Hashtbl.replace
      env.const_table
      dst
      n;

    instr





(* copy propagation *)

| ILoad(dst,Temp src) ->


    let src =
      resolve_copy env src
    in


    begin

    match get_const env src with


    | Some n ->

        kill env dst;

        Hashtbl.replace
          env.const_table
          dst
          n;

        ILoad(dst,Imm n)



    | None ->


        kill env dst;


        if dst<>src then

          Hashtbl.replace
            env.copy_table
            dst
            src;


        ILoad(dst,Temp src)

    end





| ILoad(dst,Name n) ->


    kill env dst;

    ILoad(dst,Name n)





| ILoadGlobal(dst,n) ->


    kill env dst;

    ILoadGlobal(dst,n)





(* binary constant folding *)

| IBinOp(dst,op,a,b) ->


    let a =
      resolve_copy env a
    in


    let b =
      resolve_copy env b
    in


    begin

    match get_const env a,
          get_const env b with


    | Some x,Some y ->


        begin

        match eval_binop op x y with


        | Some r ->


            kill env dst;


            Hashtbl.replace
              env.const_table
              dst
              r;


            ILoad(dst,Imm r)



        | None ->


            kill env dst;

            IBinOp(dst,op,a,b)

        end



    | ca, cb ->


        (* algebraic identities: an operand of 1 or 0, or the same temp
           on both sides, can make the operation disappear even though
           the other side is unknown *)

        begin match simplify_algebraic op ca cb a b with


        | `Const n ->


            kill env dst;

            Hashtbl.replace env.const_table dst n;

            ILoad(dst,Imm n)



        | `Copy src ->


            kill env dst;

            if dst <> src then
              Hashtbl.replace env.copy_table dst src;

            ILoad(dst,Temp src)



        | `Keep ->


        (* common subexpression elimination: reuse an earlier
           computation of the same (normalized) expression instead
           of recomputing it *)

        begin match Hashtbl.find_opt env.expr_table (bin_key op a b) with

        | Some existing ->


            kill env dst;

            if dst <> existing then
              Hashtbl.replace env.copy_table dst existing;

            ILoad(dst,Temp existing)


        | None ->


            kill env dst;

            Hashtbl.replace env.expr_table (bin_key op a b) dst;

            IBinOp(dst,op,a,b)

        end

        end

    end





(* unary folding *)

| IUnaryOp(dst,op,t) ->


    let t =
      resolve_copy env t
    in


    begin

    match get_const env t with


    | Some x ->


        begin

        match eval_unary op x with


        | Some r ->


            kill env dst;


            Hashtbl.replace
              env.const_table
              dst
              r;


            ILoad(dst,Imm r)



        | None ->


            kill env dst;

            IUnaryOp(dst,op,t)

        end



    | None ->


        begin match Hashtbl.find_opt env.unary_table (op,t) with

        | Some existing ->


            kill env dst;

            if dst <> existing then
              Hashtbl.replace env.copy_table dst existing;

            ILoad(dst,Temp existing)


        | None ->


            kill env dst;

            Hashtbl.replace env.unary_table (op,t) dst;

            IUnaryOp(dst,op,t)

        end

    end





(* function call *)

| ICall(dst,name,args) ->


    let args =
      List.map
        (resolve_copy env)
        args
    in


    clear_env env;


    kill env dst;


    ICall(dst,name,args)





| ICallVoid(name,args) ->


    let args =
      List.map
        (resolve_copy env)
        args
    in


    clear_env env;


    ICallVoid(name,args)





(* global memory write *)

| IStoreGlobal _ ->


    clear_env env;

    instr





(* control flow *)

| ILabel _
| IJump _ ->


    clear_env env;

    instr




(* fold branches on a known-constant condition into an
   unconditional jump, or drop them if never taken *)

| IBranchTrue (t, l) ->


    let t =
      resolve_copy env t
    in


    let result =
      match get_const env t with

      | Some c when c <> 0 -> IJump l

      | Some _ -> IComment "dead branch"

      | None -> IBranchTrue (t, l)
    in


    clear_env env;

    result




| IBranchFalse (t, l) ->


    let t =
      resolve_copy env t
    in


    let result =
      match get_const env t with

      | Some 0 -> IJump l

      | Some _ -> IComment "dead branch"

      | None -> IBranchFalse (t, l)
    in


    clear_env env;

    result





| IReturn _
| IComment _ ->


    instr




(* =====================================================
   Block‑level optimization (replaces constant_copy_propagation)
   ===================================================== *)

let optimize_block block =
  let env = create_env () in
  let instrs =
    List.map
      (optimize_instr env)
      block.instrs
  in
  { block with instrs }



(* =====================================================
   Unreachable block elimination

   Branch folding above can turn a conditional branch into an
   unconditional jump (or drop it entirely), which can strand
   blocks that nothing jumps to any more (dead `if (0) { ... }`
   bodies, the never-taken side of a folded `while (1)`, ...).
   Rebuild the CFG on the folded code and keep only what is
   reachable from the entry block.
   ===================================================== *)

let reachable_ids (cfg : cfg) : bool array =
  let n = Array.length cfg.blocks in
  let seen = Array.make n false in
  let queue = Queue.create () in
  seen.(cfg.entry) <- true;
  Queue.push cfg.entry queue;
  while not (Queue.is_empty queue) do
    let i = Queue.pop queue in
    List.iter
      (fun s ->
         if not seen.(s) then begin
           seen.(s) <- true;
           Queue.push s queue
         end)
      cfg.blocks.(i).succs
  done;
  seen

let prune_unreachable (body : instr list) : instr list =
  let cfg = Cfg.build body in
  let seen = reachable_ids cfg in
  Array.to_list cfg.blocks
  |> List.filter (fun b -> seen.(b.id))
  |> List.concat_map (fun b -> b.instrs)



(* =====================================================
   Dead code elimination

   Whole-function liveness (same successor/def-use shape as the
   register allocator in Codegen) so a pure instruction whose
   result is never used afterwards can be dropped. Side-effecting
   instructions (calls, global stores, control flow) are always
   kept even when their destination temp is unused.
   ===================================================== *)

module IntSet = Set.Make (Int)

let set_of_list xs =
  List.fold_left (fun set x -> IntSet.add x set) IntSet.empty xs

let instr_def = function
  | ILoad (d, _) | ILoadGlobal (d, _)
  | IBinOp (d, _, _, _) | IUnaryOp (d, _, _) -> Some d
  | ICall (d, _, _) -> Some d
  | ICallVoid _ | IStoreGlobal _ | ILabel _ | IJump _
  | IBranchTrue _ | IBranchFalse _ | IReturn _ | IComment _ -> None

let instr_uses = function
  | ILoad (_, Temp s) | IUnaryOp (_, _, s) -> [ s ]
  | ILoad (_, (Imm _ | Name _)) | ILoadGlobal _ -> []
  | IStoreGlobal (_, s) -> [ s ]
  | IBinOp (_, _, l, r) -> [ l; r ]
  | ICall (_, _, args) | ICallVoid (_, args) -> args
  | IBranchTrue (s, _) | IBranchFalse (s, _) -> [ s ]
  | IReturn (Some s) -> [ s ]
  | IReturn None | ILabel _ | IJump _ | IComment _ -> []

(* results without side effects: safe to drop when dead *)
let is_pure = function
  | ILoad _ | ILoadGlobal _ | IBinOp _ | IUnaryOp _ -> true
  | ICall _ | ICallVoid _ | IStoreGlobal _ | ILabel _ | IJump _
  | IBranchTrue _ | IBranchFalse _ | IReturn _ | IComment _ -> false

let compute_successors (body : instr array) : int list array =
  let count = Array.length body in
  let labels = Hashtbl.create 16 in
  Array.iteri
    (fun i instr ->
       match instr with
       | ILabel l -> Hashtbl.replace labels l i
       | _ -> ())
    body;
  let next i = if i + 1 < count then [ i + 1 ] else [] in
  Array.init count (fun i ->
    match body.(i) with
    | IJump l -> [ Hashtbl.find labels l ]
    | IBranchTrue (_, l) | IBranchFalse (_, l) ->
      Hashtbl.find labels l :: next i
    | IReturn _ -> []
    | _ -> next i)

let compute_live_out (body : instr array) (successors : int list array)
  : IntSet.t array =
  let count = Array.length body in
  let live_in = Array.make count IntSet.empty in
  let live_out = Array.make count IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = count - 1 downto 0 do
      let new_out =
        List.fold_left
          (fun set succ -> IntSet.union set live_in.(succ))
          IntSet.empty successors.(i)
      in
      let uses = set_of_list (instr_uses body.(i)) in
      let def =
        match instr_def body.(i) with
        | Some d -> IntSet.singleton d
        | None -> IntSet.empty
      in
      let new_in = IntSet.union uses (IntSet.diff new_out def) in
      if not (IntSet.equal new_out live_out.(i)) then begin
        live_out.(i) <- new_out;
        changed := true
      end;
      if not (IntSet.equal new_in live_in.(i)) then begin
        live_in.(i) <- new_in;
        changed := true
      end
    done
  done;
  live_out

let dead_code_eliminate (body : instr list) : instr list =
  let rec loop instrs =
    let arr = Array.of_list instrs in
    let successors = compute_successors arr in
    let live_out = compute_live_out arr successors in
    let removed = ref false in
    let kept =
      Array.to_list arr
      |> List.filteri (fun i instr ->
        let dead =
          is_pure instr
          &&
          match instr_def instr with
          | Some d -> not (IntSet.mem d live_out.(i))
          | None -> false
        in
        if dead then removed := true;
        not dead)
    in
    if !removed then loop kept else kept
  in
  loop body



(* =====================================================
   Redundant jump elimination

   `if`/`while` lowering always emits a jump around the
   alternate branch; once that branch is pruned away the jump
   simply falls into the label right after it.
   ===================================================== *)

let rec drop_redundant_jumps = function
  | IJump l1 :: (ILabel l2 :: _ as rest) when l1 = l2 ->
    drop_redundant_jumps rest
  | x :: rest -> x :: drop_redundant_jumps rest
  | [] -> []



(* =====================================================
   Local instruction scheduling (pipeline hazard reduction)

   Codegen turns every ILoad/IBinOp/IUnaryOp into a handful of
   RISC-V instructions that immediately consume the value it just
   produced (and, for spilled temps, that value comes straight out
   of memory). Feeding a result into the very next instruction is
   exactly the load-use / ALU-use pattern that stalls a simple
   in-order pipeline. Within a maximal run of pure, control-flow-
   free instructions we reorder to a different (still valid)
   topological order of the same dependency DAG, preferring an
   instruction that is *not* an immediate consumer of the value
   just scheduled whenever one is ready to run. Calls, global
   memory access and control flow are left untouched, both as
   scheduling barriers and in their original relative order, so
   their side effects and ordering can never be disturbed.
   ===================================================== *)

let is_schedulable = function
  | ILoad (_, (Imm _ | Temp _)) -> true
  | IBinOp _ | IUnaryOp _ -> true
  | ILoad (_, Name _) | ILoadGlobal _ | IStoreGlobal _
  | ICall _ | ICallVoid _ | ILabel _ | IJump _
  | IBranchTrue _ | IBranchFalse _ | IReturn _ | IComment _ -> false

let schedule_segment (instrs : instr array) : instr list =
  let n = Array.length instrs in
  if n <= 2 then Array.to_list instrs
  else begin
    let preds = Array.make n [] in
    let succs = Array.make n [] in
    let add_dep i j =
      if i <> j && not (List.mem i preds.(j)) then begin
        preds.(j) <- i :: preds.(j);
        succs.(i) <- j :: succs.(i)
      end
    in
    (* build the RAW / WAW / WAR dependency DAG over temp ids *)
    let last_writer = Hashtbl.create 16 in
    let last_readers = Hashtbl.create 16 in
    for j = 0 to n - 1 do
      let uses = instr_uses instrs.(j) in
      List.iter
        (fun t ->
           match Hashtbl.find_opt last_writer t with
           | Some i -> add_dep i j (* RAW *)
           | None -> ())
        uses;
      (match instr_def instrs.(j) with
       | Some d ->
         (match Hashtbl.find_opt last_writer d with
          | Some i -> add_dep i j (* WAW *)
          | None -> ());
         (match Hashtbl.find_opt last_readers d with
          | Some readers -> List.iter (fun i -> add_dep i j (* WAR *)) readers
          | None -> ());
         Hashtbl.replace last_writer d j;
         Hashtbl.replace last_readers d []
       | None -> ());
      List.iter
        (fun t ->
           let prev =
             match Hashtbl.find_opt last_readers t with
             | Some l -> l
             | None -> []
           in
           Hashtbl.replace last_readers t (j :: prev))
        uses
    done;
    (* greedy list scheduling: among the ready instructions, avoid
       picking a direct consumer of the instruction just emitted
       whenever some other ready instruction is available *)
    let remaining = Array.map List.length preds in
    let ready = ref (List.filter (fun i -> remaining.(i) = 0) (List.init n Fun.id)) in
    let out = ref [] in
    let last = ref (-1) in
    for _ = 1 to n do
      let is_direct_consumer i = !last >= 0 && List.mem !last preds.(i) in
      let chosen =
        match List.filter (fun i -> not (is_direct_consumer i)) !ready with
        | i :: _ -> i
        | [] -> List.hd !ready
      in
      ready := List.filter (fun i -> i <> chosen) !ready;
      out := instrs.(chosen) :: !out;
      last := chosen;
      List.iter
        (fun s ->
           remaining.(s) <- remaining.(s) - 1;
           if remaining.(s) = 0 then ready := s :: !ready)
        succs.(chosen)
    done;
    List.rev !out
  end

let rec schedule_block = function
  | [] -> []
  | (x :: rest) as instrs ->
    if not (is_schedulable x) then x :: schedule_block rest
    else begin
      let rec split_segment acc = function
        | y :: ys when is_schedulable y -> split_segment (y :: acc) ys
        | tail -> (List.rev acc, tail)
      in
      let segment, tail = split_segment [] instrs in
      schedule_segment (Array.of_list segment) @ schedule_block tail
    end



(* =====================================================
   Loop-invariant constant hoisting

   A loop condition like `i < 100` reloads the 100 on every single
   iteration, which in a three-instruction loop body is a third of the
   work. A constant load reads nothing, so it is invariant in any loop
   containing it and can move to a preheader.

   This runs before rotation, while a loop still starts with its header
   label reached by fall-through from above -- that makes the slot just
   before the header a valid preheader. After rotation the loop is
   entered by a jump over the body, so the same slot would be dead code.
   ===================================================== *)

let hoist_loop_constants (body : instr list) : instr list =
  let arr = Array.of_list body in
  let n = Array.length arr in
  let label_index = Hashtbl.create 16 in
  Array.iteri
    (fun i instr ->
       match instr with
       | ILabel l -> Hashtbl.replace label_index l i
       | _ -> ())
    arr;
  let def_count = Hashtbl.create 64 in
  Array.iter
    (fun instr ->
       match instr_def instr with
       | Some d ->
         Hashtbl.replace def_count d
           (1 + Option.value ~default:0 (Hashtbl.find_opt def_count d))
       | None -> ())
    arr;
  (* For each instruction, the header of the outermost loop enclosing it.
     A transfer to a label at or before it closes a loop over that span. *)
  let header = Array.make n (-1) in
  Array.iteri
    (fun i instr ->
       let target =
         match instr with
         | IJump l | IBranchTrue (_, l) | IBranchFalse (_, l) ->
           Hashtbl.find_opt label_index l
         | _ -> None
       in
       match target with
       | Some j when j <= i ->
         for k = j to i do
           if header.(k) = -1 || j < header.(k) then header.(k) <- j
         done
       | _ -> ())
    arr;
  let hoisted = Array.make n [] in
  let removed = Array.make n false in
  Array.iteri
    (fun k instr ->
       match instr with
       | ILoad (t, Imm _)
         when header.(k) >= 0
              && header.(k) < k
              && Hashtbl.find_opt def_count t = Some 1 ->
         let j = header.(k) in
         hoisted.(j) <- hoisted.(j) @ [ instr ];
         removed.(k) <- true
       | _ -> ())
    arr;
  let out = ref [] in
  Array.iteri
    (fun i instr ->
       List.iter (fun h -> out := h :: !out) hoisted.(i);
       if not removed.(i) then out := instr :: !out)
    arr;
  List.rev !out



(* =====================================================
   Loop rotation

   `while` lowers to a test at the top and an unconditional jump back
   to it, so every iteration pays two control transfers: the test
   falling through, and the jump home. Moving the test to the bottom
   leaves one taken branch per iteration and drops the jump:

     jump COND            COND:  <test>
     TOP:  <body>   <==   branch-if-false END
     COND: <test>         <body>
     branch-if-true TOP   jump COND
     END:                 END:

   Both labels keep their original meaning -- COND still re-evaluates
   the test and END still sits past the loop -- so `continue` and
   `break` inside the body need no adjustment.
   ===================================================== *)

let rotate_counter = ref 0

(* Condition code must be straight-line: a label inside it could be
   jumped to from elsewhere, and moving it below the body would change
   where that lands. Short-circuit conditions (&&, ||) build their own
   labels and so are left alone. *)
let rec take_cond acc = function
  | IBranchFalse (c, endl) :: rest -> Some (List.rev acc, c, endl, rest)
  | (ILabel _ | IJump _ | IBranchTrue _ | IReturn _) :: _ -> None
  | x :: rest -> take_cond (x :: acc) rest
  | [] -> None

(* Labels are globally unique, so matching the loop's own back edge
   cannot pick up a nested loop's. *)
let rec take_body cond endl acc = function
  | IJump l :: ILabel e :: rest when l = cond && e = endl ->
    Some (List.rev acc, rest)
  | x :: rest -> take_body cond endl (x :: acc) rest
  | [] -> None

let rec rotate_loops instrs =
  match instrs with
  | ILabel cond :: rest ->
    let rotated =
      match take_cond [] rest with
      | Some (cond_instrs, c, endl, after) ->
        (match take_body cond endl [] after with
         | Some (body, tail) ->
           let n = !rotate_counter in
           incr rotate_counter;
           let top = Printf.sprintf ".Lloop_top%d" n in
           Some
             (List.concat
                [ [ IJump cond; ILabel top ];
                  rotate_loops body;
                  [ ILabel cond ];
                  cond_instrs;
                  [ IBranchTrue (c, top); ILabel endl ];
                  rotate_loops tail ])
         | None -> None)
      | None -> None
    in
    (match rotated with
     | Some result -> result
     | None -> ILabel cond :: rotate_loops rest)
  | x :: rest -> x :: rotate_loops rest
  | [] -> []



(* =====================================================
   Function
   ===================================================== *)

let optimize_func f =
  (* Folding runs first, while a constant condition still sits in the
     same block as the branch reading it -- hoisting the constant out to
     a preheader would put a label between them and lose the value, so a
     `while (0)` would survive as real code. *)
  let cfg = Cfg.build f.body in
  let blocks =
    Array.map optimize_block cfg.blocks
  in
  let folded =
    Array.to_list blocks
    |> List.concat_map (fun b -> b.instrs)
    |> List.filter (function IComment _ -> false | _ -> true)
  in
  let live = prune_unreachable folded in
  (* Reshaping the loops that are left. Hoisting needs the pre-rotation
     shape, where the header is still reached by fall-through. *)
  let shaped = rotate_loops (hoist_loop_constants live) in
  let body =
    dead_code_eliminate shaped
    |> drop_redundant_jumps
    |> schedule_block
  in
  { f with body }



(* =====================================================
   Program
   ===================================================== *)

let run (p : program) : program =
  { p with funcs = List.map optimize_func p.funcs }