type dominance_map = (string * string list) list

type dominance_tree =
  | Leaf
  | Node of string * dominance_tree list

let dominators (cfg : Bril.cfg) : dominance_map =
  [] (* TODO *)

let dominance_tree (cfg : Bril.cfg) (doms : dominance_map) : dominance_tree =
  Leaf

let frontiers (cfg : Bril.cfg) (doms : dominance_map) : dominance_map =
  [] (* TODO *)

let ssa_of_bril (bril : Bril.t) : Bril.t =
  bril (* TODO *)

let bril_of_ssa (bril : Bril.t) : Bril.t =
  bril (* TODO *)