open Core

type dominance_map = (string * string list) list

type dominance_tree =
  | Leaf
  | Node of string * dominance_tree list

let equal = String.equal

let mem e l= List.exists l ~f:(fun s -> equal s e)

let get_preds (v : string) (cfg : Bril.cfg) : string list =
  cfg.blocks
  |> List.map ~f:fst
  |> List.filter ~f:(fun n -> List.Assoc.find_exn cfg.edges n ~equal |> mem v)

let get_dominance_map (cfg : Bril.cfg) : dominance_map =
  let nodes = List.map ~f:fst cfg.blocks in
  let init = List.map ~f:(fun v -> v, nodes) nodes in
  let rec f acc =
    let update (v, doms) =
      let preds = get_preds v cfg in
      if Int.equal (List.length preds) 0 then v, [v]
      else
        let pred = List.hd_exn preds in
        let doms = pred
          |> List.Assoc.find_exn acc ~equal
          |> List.filter ~f:(fun n -> List.for_all preds
            ~f:(fun pred -> mem n (List.Assoc.find_exn acc pred ~equal))) in
        v, if mem v doms then doms else v :: doms in
    let acc' = List.map ~f:update acc in
    let changed = List.for_all acc'
      ~f:(fun (v, doms) -> Int.equal (List.length doms)
        (List.Assoc.find_exn acc v ~equal |> List.length)) in
    if not changed then f acc' else acc' in
  f init

let is_immediate (doms : dominance_map) (a : string) (b : string) : bool =
  let nodes = List.map doms ~f:fst in
  let neq = not (equal a b) in
  let bdoms = List.Assoc.find_exn doms b ~equal in
  let cond = List.for_all nodes ~f:(fun n -> not (mem n bdoms) || equal n a)  in
  neq && cond

let dominance_tree (cfg : Bril.cfg) (doms : dominance_map) : dominance_tree =
  let nodes = List.map cfg.blocks ~f:fst in
  let entry = List.hd_exn cfg.blocks |> fst in
  let rec f v =
    let vdominates =
      List.filter nodes ~f:(fun n -> List.Assoc.find_exn doms n ~equal |> mem v) in
    let vimm_dominates =
      List.filter vdominates ~f:(fun b -> is_immediate doms v b) in
    Node (v, List.map vimm_dominates ~f) in
  f entry

let is_frontier (cfg : Bril.cfg) (doms : dominance_map) (a : string)
    (b : string) : bool =
  let nodes = List.map cfg.blocks ~f:fst in
  let bpreds =
    List.filter nodes ~f:(fun n -> List.Assoc.find_exn cfg.edges n ~equal |> mem b) in
  let bdoms = List.Assoc.find_exn doms b ~equal in
  let adomsb = mem a bdoms in
  let adoms_predb =
    List.exists bpreds ~f:(fun n -> List.Assoc.find_exn doms n ~equal |> mem a) in
  not adomsb && adoms_predb

let get_frontiers (cfg : Bril.cfg) (doms : dominance_map) : dominance_map =
  let nodes = List.map cfg.blocks ~f:fst in
  let f n = n, List.filter nodes ~f:(fun v -> is_frontier cfg doms n v) in
  List.map nodes ~f

let add_labels (bril : Bril.t) : Bril.t =
  bril (* TODO *)

let ssa_of_bril (bril : Bril.t) : Bril.t =
  bril (* TODO *)

let bril_of_ssa (bril : Bril.t) : Bril.t =
  bril (* TODO *)