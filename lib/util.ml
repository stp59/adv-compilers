open Core

let equal = String.equal

let mem e l= List.exists l ~f:(fun s -> equal s e)

(** [get_preds block cfg] is a list of blocks that precede [block] in [cfg] *)
let get_preds (block : string) (cfg : Bril.cfg) : string list =
  cfg.blocks
  |> List.map ~f:fst
  |> List.filter ~f:(fun n -> List.Assoc.find_exn cfg.edges n ~equal |> mem block)

(** [get_vars args cfg] is a list of all the variables (and their types) that
    appear in the [cfg], including the [args]. *)
let get_vars (args : Bril.dest list) (cfg : Bril.cfg) : Bril.dest list =
  let get_instr_vars acc instr =
    let def = match instr with
      | Bril.Const (dest, _) | Bril.Binary (dest, _, _, _)
      | Bril.Unary (dest, _, _) | Bril.Call (Some dest, _, _)
      | Bril.Phi (dest, _, _, _) -> Some dest
      | _ -> None in
    Option.value_map def ~default:acc
      ~f:(fun (v, t) -> List.Assoc.add acc v t ~equal) in
  let get_block_vars acc (l, b) =
    List.fold b ~init:acc ~f:get_instr_vars in
  List.fold cfg.blocks ~init:args ~f:get_block_vars