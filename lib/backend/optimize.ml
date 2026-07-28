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
| IJump _
| IBranchTrue _
| IBranchFalse _ ->


    clear_env env;

    instr





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
   Function
   ===================================================== *)

let optimize_func f =
  let cfg = Cfg.build f.body in
  let blocks =
    Array.map optimize_block cfg.blocks
  in
  let body =
    Array.to_list blocks
    |> List.concat_map (fun b -> b.instrs)
  in
  { f with body }



(* =====================================================
   Program
   ===================================================== *)

let run p = p