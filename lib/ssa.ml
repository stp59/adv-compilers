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

let add_label (n, is : string * Bril.instr list) : string * Bril.instr list =
  match List.hd_exn is with
  | Label _ -> n, is
  | _ -> n, Label n :: is

let add_labels_instrs (intrs : Bril.instr list) : Bril.instr list =
  let cfg = Bril.to_blocks_and_cfg intrs in
  let blocks = List.map cfg.blocks ~f:add_label in
  List.fold blocks ~init:[] ~f:(fun acc (_, is) -> acc @ is)

let add_labels_func (func : Bril.func) : Bril.func =
  { func with instrs = add_labels_instrs func.instrs }

let add_labels (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:add_labels_func }

let get_vars (args : Bril.dest list) (instrs : Bril.instr list) : Bril.dest list =
  let f acc instr =
    let def = match instr with
      | Bril.Const (dest, _) | Bril.Binary (dest, _, _, _)
      | Bril.Unary (dest, _, _) | Bril.Call (Some dest, _, _)
      | Bril.Phi (dest, _, _) -> Some dest
      | _ -> None in
    Option.value_map def ~default:acc
      ~f:(fun (v, t) -> List.Assoc.add acc v t ~equal) in
  List.fold instrs ~init:args ~f

let defs_var (v : string) (instrs : Bril.instr list) : bool =
  let f instr =
    match instr with
    | Bril.Const ((dest, _), _) | Bril.Binary ((dest, _), _, _, _)
    | Bril.Unary ((dest, _), _, _) | Bril.Call (Some (dest, _), _, _)
    | Bril.Phi ((dest, _), _, _) -> equal dest v
    | _ -> false in
  List.exists instrs ~f

let get_var_defs (v : string) (cfg : Bril.cfg) : string list =
  let nodes = List.map cfg.blocks ~f:fst in
  List.filter nodes
    ~f:(fun n -> List.Assoc.find_exn cfg.blocks n ~equal |> defs_var v)

let insert_phis (args : Bril.dest list) (instrs : Bril.instr list) : Bril.instr list =
  let vars = get_vars args instrs in
  let cfg = Bril.to_blocks_and_cfg instrs in
  let doms = get_dominance_map cfg in
  let fronts = get_frontiers cfg doms in
  let cfg' =
    List.fold vars ~init:cfg ~f:(fun cfg (var, t) ->
      let defs = get_var_defs var cfg in
      List.fold defs ~init:cfg ~f:(fun cfg def ->
        let deffronts = List.Assoc.find_exn fronts def ~equal in
        List.fold deffronts ~init:cfg ~f:(fun cfg front ->
          let blck = List.Assoc.find_exn cfg.blocks front ~equal in
          let blck' = match List.hd_exn blck with
            | Phi ((dest, t), args, ls) when (equal dest var) ->
              Bril.Phi ((var, t), var :: args, def :: ls) :: List.tl_exn blck
            | _ -> Phi ((var, t), [var], [def]) :: blck in
          { cfg with blocks = List.Assoc.add cfg.blocks front blck' ~equal }))) in
  List.fold cfg'.blocks ~init:[] ~f:(fun acc (_, is) -> acc @ is)

let rename_vars (args : Bril.dest list) (instrs : Bril.instr list) : Bril.instr list =
  instrs (* TODO *)

let ssa_of_instrs (args : Bril.dest list) (instrs : Bril.instr list) : Bril.instr list =
  instrs |> insert_phis args |> rename_vars args

let ssa_of_func (func : Bril.func) : Bril.func =
  { func with instrs = ssa_of_instrs func.args func.instrs }

let ssa_of_bril (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:ssa_of_func }

let bril_of_ssa (bril : Bril.t) : Bril.t =
  bril (* TODO *)