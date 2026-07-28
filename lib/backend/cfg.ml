(** Control Flow Graph for ToyC IR *)

open Ir


(* ================================
   Basic Block
   ================================ *)

type block = {
  id : int;

  (* block入口label，如果存在 *)
  label : string option;

  (* block内部IR *)
  instrs : instr list;


  (* 后继节点 *)
  mutable succs : int list;


  (* 前驱节点 *)
  mutable preds : int list;
}



type cfg = {
  blocks : block array;

  (* 入口block编号 *)
  entry : int;
}



(* ================================
   Step 1:
   Split instruction list
   into basic blocks
   ================================ *)


let build_blocks (body : instr list) : block list =

  let blocks = ref [] in

  let current = ref [] in

  let current_label = ref None in


  let finish_block () =

    match !current with

    | [] -> ()

    | xs ->

        let id =
          List.length !blocks
        in

        let b =
          {
            id;

            label = !current_label;

            instrs =
              List.rev xs;

            succs = [];

            preds = [];
          }
        in


        blocks :=
          b :: !blocks;


        current := [];

        current_label := None

  in



  List.iter
    (fun instr ->

      match instr with


      (* label starts new block *)
      | ILabel l ->

          finish_block ();

          current_label :=
            Some l;

          current :=
            [instr]


      (* control transfer ends block *)
      | IJump _
      | IBranchTrue _
      | IBranchFalse _
      | IReturn _ ->

          current :=
            instr :: !current;

          finish_block ()



      (* ordinary instruction *)
      | _ ->

          current :=
            instr :: !current

    )
    body;


  finish_block ();


  List.rev !blocks





(* ================================
   label -> block id
   ================================ *)

let build_label_map blocks =

  let map =
    Hashtbl.create 32
  in


  List.iter
    (fun b ->

      match b.label with

      | Some l ->
          Hashtbl.replace
            map l b.id

      | None ->
          ()

    )
    blocks;


  map





(* ================================
   Step 2:
   connect CFG edges
   ================================ *)

let build_edges blocks =

  let label_map =
    build_label_map blocks
  in


  let arr =
    Array.of_list blocks
  in


  let n =
    Array.length arr
  in



  for i = 0 to n - 1 do

    let b =
      arr.(i)
    in


    match List.rev b.instrs with


    (* unconditional jump *)
    | IJump l :: _ ->

        let dst =
          Hashtbl.find label_map l
        in

        b.succs <-
          [dst]



    (* conditional branch:
       true/false two paths
    *)
    | IBranchTrue (_, l) :: _
    | IBranchFalse (_, l) :: _ ->


        let dst =
          Hashtbl.find label_map l
        in


        b.succs <-
          dst ::
          (
            if i + 1 < n
            then [i+1]
            else []
          )



    (* return ends control flow *)
    | IReturn _ :: _ ->

        b.succs <- []



    (* normal block flows next *)
    | _ ->

        if i + 1 < n then
          b.succs <- [i+1]

  done;



  (* build predecessors *)

  Array.iter
    (fun b ->

      List.iter
        (fun s ->

          arr.(s).preds <-
            b.id ::
            arr.(s).preds

        )
        b.succs

    )
    arr;



  arr





(* ================================
   Public interface
   ================================ *)

let build body =

  let blocks =
    build_blocks body
  in


  {
    blocks =
      build_edges blocks;

    entry = 0;
  }