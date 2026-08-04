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


type env =
{
  const_table:(int,int) Hashtbl.t;

  copy_table:(int,int) Hashtbl.t;
}



let create_env () =
{
 const_table=Hashtbl.create 64;
 copy_table=Hashtbl.create 64;
}



let clear_env env =
(
 Hashtbl.clear env.const_table;
 Hashtbl.clear env.copy_table
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
   !dead



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



    | _ ->


        kill env dst;

        IBinOp(dst,op,a,b)

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


        kill env dst;

        IUnaryOp(dst,op,t)

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
   Function
   ===================================================== *)

let optimize_func f =
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
  let body = dead_code_eliminate live |> drop_redundant_jumps in
  { f with body }



(* =====================================================
   Program
   ===================================================== *)

let run (p : program) : program =
  { p with funcs = List.map optimize_func p.funcs }