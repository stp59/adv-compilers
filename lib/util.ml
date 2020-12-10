open Core

type dominance_map = (string * string list) list

let equal = String.equal

let mem e l= List.exists l ~f:(fun s -> equal s e)

(** [get_preds block cfg] is a list of blocks that precede [block] in [cfg] *)
let get_preds (block : string) (cfg : Bril.cfg) : string list =
  cfg.blocks
  |> List.map ~f:fst
  |> List.filter ~f:(fun n -> List.Assoc.find_exn cfg.edges n ~equal |> mem block)

(** [defs_var v instrs] is [true] iff. the intructions [instrs] write to the
    variable [var]. *)
let defs_var (v : string) (instrs : Bril.instr list) : bool =
  let f instr =
    match instr with
    | Bril.Const ((dest, _), _) | Bril.Binary ((dest, _), _, _, _)
    | Bril.Unary ((dest, _), _, _) | Bril.Call (Some (dest, _), _, _)
    | Bril.Phi ((dest, _), _, _, _) ->
      equal (String.split_on_chars ~on:['.'] dest |> List.hd_exn) v
    | _ -> false in
  List.exists instrs ~f

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

let is_reachable (cfg : Bril.cfg) (entry : string) (b : string) : bool =
  let preds = get_preds b cfg in 
  not (List.is_empty preds) || (equal entry b)

(** [get_dominance_map cfg] is a map from blocks [b] to a list of blocks which
    dominate [b] in the [cfg]. *)
let get_dominance_map (cfg : Bril.cfg) : dominance_map =
  let nodes = List.map ~f:fst cfg.blocks in
  let init = List.map ~f:(fun v -> v, nodes) nodes in
  let rec f acc =
    let update acc v =
      let preds = get_preds v cfg in
      if Int.equal (List.length preds) 0
      then List.Assoc.add acc v [v] ~equal
      else
        let pred = List.hd_exn preds in
        let doms = pred
          |> List.Assoc.find_exn acc ~equal
          |> List.filter ~f:(fun n -> List.for_all preds
            ~f:(fun pred -> mem n (List.Assoc.find_exn acc pred ~equal))) in
        List.Assoc.add acc v (if mem v doms then doms else v :: doms) ~equal in
    let acc' = List.fold ~init:acc ~f:update nodes in
    let unchanged = List.for_all nodes
      ~f:(fun v -> Int.equal (List.Assoc.find_exn acc' v ~equal |> List.length)
          (List.Assoc.find_exn acc v ~equal |> List.length)) in
    if unchanged then acc' else f acc' in
  f init

(** [stricly_dominates doms a b] is [true] iff. [a] strictly dominates [b]
    according to the dominator map [doms]. *)
let strictly_dominates (doms : dominance_map) (a : string) (b : string) : bool =
  let bdoms = List.Assoc.find_exn doms b ~equal in
  mem a bdoms && not (equal a b)

(** [is_immediate doms a b] is [true] iff. [a] immediately dominates [b]
    according to the dominator map [doms]. *)
let is_immediate (doms : dominance_map) (a : string) (b : string) : bool =
  let nodes = List.map doms ~f:fst in
  let bdoms = List.Assoc.find_exn doms b ~equal in
  let adomsb = mem a bdoms && not (equal a b) in
  let f n =
    let ndomsb = strictly_dominates doms n b in
    let adomsn = strictly_dominates doms a n in
    adomsn && ndomsb in
  let cond = List.exists nodes ~f in
  adomsb && not cond

(** [is_frontier cfg doms a b] is [true] iff. [b] is in the dominance frontier
    of [a] in the [cfg]. *)
let is_frontier (cfg : Bril.cfg) (a : string) (b : string) : bool =
  let doms = get_dominance_map cfg in
  let bpreds = get_preds b cfg in
  let bdoms = List.Assoc.find_exn doms b ~equal in
  let adomsb = mem a bdoms && not (equal a b) in
  let adoms_predb =
    List.exists bpreds ~f:(fun n -> List.Assoc.find_exn doms n ~equal |> mem a) in
  (not adomsb) && adoms_predb

(** [get_frontiers cfg] is a map from blocks [b] to lists of blocks which are in
    the dominance frontier of [b] in the [cfg]. *)
let get_frontiers (cfg : Bril.cfg) : dominance_map =
  let nodes = List.map cfg.blocks ~f:fst in
  let f n = n, List.filter nodes ~f:(fun v -> is_frontier cfg n v) in
  List.map nodes ~f