(** Backward live-variable analysis over the instruction-level CFG.

    live_in(i)  = uses(i) U (live_out(i) \ defs(i))
    live_out(i) = U { live_in(s) | s in succs(i) }

    Both the dead-definition pass and the register allocator read the result. *)

module IntSet = Cfg.IntSet

type t = {
  live_in : IntSet.t array;
  live_out : IntSet.t array;
}

let analyze (cfg : Cfg.t) =
  let count = Array.length cfg.instrs in
  let live_in = Array.make count IntSet.empty in
  let live_out = Array.make count IntSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    (* Iterating backwards converges in far fewer sweeps for straight-line code. *)
    for index = count - 1 downto 0 do
      let out_set =
        List.fold_left
          (fun acc succ -> IntSet.union acc live_in.(succ))
          IntSet.empty cfg.succs.(index)
      in
      let in_set =
        IntSet.union cfg.uses.(index) (IntSet.diff out_set cfg.defs.(index))
      in
      if not (IntSet.equal out_set live_out.(index)) then begin
        live_out.(index) <- out_set;
        changed := true
      end;
      if not (IntSet.equal in_set live_in.(index)) then begin
        live_in.(index) <- in_set;
        changed := true
      end
    done
  done;
  { live_in; live_out }
