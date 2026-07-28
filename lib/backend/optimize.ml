(** Safe optimization passes for ToyC IR *)

open Ir
module A = Ast


(* =====================================================
   Constant evaluation
   ===================================================== *)

let eval_binop op a b =
  match op with
  | A.Add ->
      Some (a + b)

  | A.Sub ->
      Some (a - b)

  | A.Mul ->
      Some (a * b)

  | A.Div ->
      if b = 0 then None
      else if a = min_int && b = -1 then None
      else Some (a / b)

  | A.Mod ->
      if b = 0 then None
      else Some (a mod b)


  | A.Lt ->
      Some (if a < b then 1 else 0)

  | A.Gt ->
      Some (if a > b then 1 else 0)

  | A.Le ->
      Some (if a <= b then 1 else 0)

  | A.Ge ->
      Some (if a >= b then 1 else 0)

  | A.Eq ->
      Some (if a = b then 1 else 0)

  | A.Ne ->
      Some (if a <> b then 1 else 0)

  | A.And ->
      Some (if a <> 0 && b <> 0 then 1 else 0)

  | A.Or ->
      Some (if a <> 0 || b <> 0 then 1 else 0)



let eval_unary op a =
  match op with

  | A.UPlus ->
      Some a

  | A.UMinus ->
      if a = min_int then None
      else Some (-a)

  | A.Not ->
      Some (if a = 0 then 1 else 0)



(* =====================================================
   Constant table
   only records real constants
   NO copy propagation
   ===================================================== *)

type env = (int, int) Hashtbl.t



let get_const env t =
  Hashtbl.find_opt env t



let kill env t =
  Hashtbl.remove env t



let clear env =
  Hashtbl.clear env



(* =====================================================
   Constant folding
   ===================================================== *)

let optimize_instr env instr =

  match instr with


  (* t = immediate *)
  | ILoad(dst, Imm n) ->

      Hashtbl.replace env dst n;
      instr



  (* t = another temp
     
     IMPORTANT:
     Do NOT propagate.
     Because temp can be overwritten.
     
     Example:
       t1=t0
       t0=5
     
     t1 is not necessarily 5.
  *)
  | ILoad(dst, Temp _) ->

      kill env dst;
      instr



  (* load address/global *)
  | ILoad(dst, Name _) ->

      kill env dst;
      instr



  | ILoadGlobal(dst, _) ->

      kill env dst;
      instr



  (* binary operation *)
  | IBinOp(dst, op, a, b) ->

      begin
        match get_const env a,
              get_const env b with


        | Some x, Some y ->

            begin
              match eval_binop op x y with

              | Some r ->

                  Hashtbl.replace env dst r;

                  ILoad(dst, Imm r)


              | None ->

                  kill env dst;

                  instr
            end



        | _ ->

            kill env dst;

            instr
      end



  (* unary operation *)
  | IUnaryOp(dst, op, t) ->

      begin
        match get_const env t with


        | Some x ->

            begin
              match eval_unary op x with

              | Some r ->

                  Hashtbl.replace env dst r;

                  ILoad(dst, Imm r)


              | None ->

                  kill env dst;

                  instr
            end



        | None ->

            kill env dst;

            instr
      end



  (* calls may change everything *)
  | ICall(dst, _, _) ->

      clear env;
      kill env dst;
      instr



  | ICallVoid _ ->

      clear env;
      instr



  (* global write *)
  | IStoreGlobal _ ->

      clear env;
      instr



  (* control flow boundary

     We cannot know which path arrives here.
  *)
  | ILabel _
  | IJump _
  | IBranchTrue _
  | IBranchFalse _ ->

      clear env;
      instr



  | IReturn _
  | IComment _ ->

      instr





let constant_fold body =

  let env =
    Hashtbl.create 32
  in

  List.map
    (optimize_instr env)
    body





(* =====================================================
   Function / Program
   ===================================================== *)

let optimize_func (f : func_ir) =

  let body =
    constant_fold f.body
  in

  {
    f with
    body
  }



let run (p : program) : program =

  {
    p with

    funcs =
      List.map optimize_func p.funcs
  }
