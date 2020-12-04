open Core

let equal = String.equal

let mem e l= List.exists l ~f:(fun s -> equal s e)

(** [get_preds block cfg] is a list of blocks that precede [block] in [cfg] *)
let get_preds (block : string) (cfg : Bril.cfg) : string list =
  cfg.blocks
  |> List.map ~f:fst
  |> List.filter ~f:(fun n -> List.Assoc.find_exn cfg.edges n ~equal |> mem block)