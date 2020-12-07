open Core
open Util

let add_label (n, is : string * Bril.instr list) : string * Bril.instr list =
  match List.hd_exn is with
  | Label _ -> n, is
  | _ -> n, Label n :: is

let add_labels_instrs (intrs : Bril.instr list) : Bril.instr list =
  let cfg = Bril.to_blocks_and_cfg intrs in
  let blocks = List.map cfg.blocks ~f:add_label |> List.map ~f:snd in
  List.fold blocks ~init:[] ~f:(@)

let add_labels_func (func : Bril.func) : Bril.func =
  { func with instrs = add_labels_instrs func.instrs }

let add_labels (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:add_labels_func }

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

(** [get_var_defs v args cfg] is a list of blocks in the [cfg] which write to
    the variable [v]. Each of the [args] is treated as having been written to
    in the entry block. *)
let get_var_defs (v : string) args (cfg : Bril.cfg) : string list =
  let nodes = List.map cfg.blocks ~f:fst in
  let entry = List.hd_exn nodes in
  let is_arg = List.exists args ~f:(fun (x,_) -> equal x v) in
  let f n =
    let is = List.Assoc.find_exn cfg.blocks n ~equal in
    (defs_var v is) || (is_arg && equal n entry) in
  List.filter nodes ~f

(** [insert_phis args cfg doms] is a partially transformed version of [cfg] with
    phi-nodes inserted for SSA in the proper locations, but without renamed
    variables or proper phi node reads. *)
let insert_phis (args : Bril.dest list) (cfg : Bril.cfg) doms : Bril.cfg =
  let vars = get_vars args cfg in
  let fronts = get_frontiers cfg in
  List.fold vars ~init:cfg ~f:(fun cfg (var, t) ->
    let defs = get_var_defs var args cfg in
    let rec f acc cfg defs =
      let defs', cfg = List.fold acc ~init:([], cfg) ~f:(fun (defs', cfg) def ->
        let deffronts = List.Assoc.find_exn fronts def ~equal in
        List.fold deffronts ~init:([], cfg) ~f:(fun (defs', cfg) front ->
          let blck = List.Assoc.find_exn Bril.(cfg.blocks) front ~equal in
          let blck' = match blck with
            | Label _ :: Phi ((dest, t), _, _, _) :: _ when (equal dest var) -> blck
            | Label l :: tl -> Label l :: Phi ((var, t), [], [], (var, t)) :: tl
            | _ -> Phi ((var, t), [], [], (var, t)) :: blck in
          let changed = List.length defs > 1 in
          let blck' = if changed then blck' else blck in
          let cfg = { cfg with blocks = List.Assoc.add cfg.blocks front blck' ~equal } in
          let defs' = if not (mem front defs) && changed then front :: defs' else defs' in
          defs', cfg)) in
      if List.is_empty defs' then cfg else f defs' cfg (defs @ defs') in
    f defs cfg defs)

(** [block_defs_var cfg block var] is [true] iff. the [block] writes to the 
    variable [var] according to the [cfg]. *)
let block_defs_var (cfg : Bril.cfg) (block : string) (var : string) : bool =
  defs_var var (List.Assoc.find_exn cfg.blocks block ~equal)

(** [rename_vars args cfg doms entry] is the SSA version of [cfg].
    Precondition: the [cfg] was output from the [insert_phis] function. *)
let rename_vars (args : Bril.dest list) (cfg : Bril.cfg) doms entry : Bril.cfg =
  let nodes = List.map cfg.blocks ~f:fst in
  let vars = get_vars args cfg |> List.map ~f:fst in
  let stacks = List.map vars ~f:(fun v -> v, [v]) in
  let counters = List.map vars ~f:(fun v -> v, let box = ref (-1) in fun () -> box := !box + 1; !box) in
  let rename_instr stack i =
    let open Bril in
    match i with
    | Label l -> stack, Label l
    | Const ((v, t), c) ->
      let fresh = v ^ "." ^ (List.Assoc.find_exn counters v ~equal () |> string_of_int) in 
      List.Assoc.add stack v ~equal (fresh :: List.Assoc.find_exn stack v ~equal),
      Const ((fresh, t), c)
    | Binary ((v, t), o, a1, a2) ->
      let fresh = v ^ "." ^ (List.Assoc.find_exn counters v ~equal () |> string_of_int) in
      List.Assoc.add stack v ~equal (fresh :: List.Assoc.find_exn stack v ~equal),
      Binary ((fresh, t), o,
        List.Assoc.find_exn stack a1 ~equal |> List.hd_exn,
        List.Assoc.find_exn stack a2 ~equal |> List.hd_exn)
    | Unary ((v, t), o, a) ->
      let fresh = v ^ "." ^ (List.Assoc.find_exn counters v ~equal () |> string_of_int) in
      List.Assoc.add stack v ~equal (fresh :: List.Assoc.find_exn stack v ~equal),
      Unary ((fresh, t), o, List.Assoc.find_exn stack a ~equal |> List.hd_exn)
    | Jmp l -> stack, Jmp l
    | Br (a, l1, l2) ->
      stack, Br (List.Assoc.find_exn stack a ~equal |> List.hd_exn, l1, l2)
    | Call (Some (v, t), f, args) ->
      let fresh = v ^ "." ^ (List.Assoc.find_exn counters v ~equal () |> string_of_int) in
      List.Assoc.add stack v ~equal (fresh :: List.Assoc.find_exn stack v ~equal),
      Call (Some (fresh, t), f, List.map args
        ~f:(fun a -> List.Assoc.find_exn stack a ~equal |> List.hd_exn))
    | Call (None, f, args) ->
      stack, Call (None, f, List.map args
        ~f:(fun a -> List.Assoc.find_exn stack a ~equal |> List.hd_exn))
    | Ret (Some a) ->
      stack, Ret (Some (List.Assoc.find_exn stack a ~equal |> List.hd_exn))
    | Ret None -> stack, Ret None
    | Print args ->
      stack, Print (List.map args
        ~f:(fun a -> List.Assoc.find_exn stack a ~equal |> List.hd_exn))
    | Nop -> stack, Nop
    | Phi ((v, t), args, ls, (v', t')) ->
      let fresh = v ^ "." ^ (List.Assoc.find_exn counters v ~equal () |> string_of_int) in
      List.Assoc.add stack v ~equal (fresh :: List.Assoc.find_exn stack v ~equal),
      Phi ((fresh, t), args, ls, (v', t')) in
  let rename_phi stacks block (cfg : Bril.cfg) succ =
    let is = List.Assoc.find_exn cfg.blocks succ ~equal in
    let f i =
      match i with
      | Bril.Phi ((v, t), args, ls, (v', t')) ->
        Bril.Phi ((v, t),
          (List.Assoc.find_exn stacks v' ~equal |> List.hd_exn) :: args,
          block :: ls,
          (v', t'))
      | _ -> i in
    let is = List.map is ~f in
    { cfg with blocks = List.Assoc.add cfg.blocks succ is ~equal } in
  let rec rename_block block (cfg : Bril.cfg) stacks =
    let is = List.Assoc.find_exn cfg.blocks block ~equal in
    let (stacks', is) = List.fold_map is ~init:stacks ~f:rename_instr in
    let succs = List.Assoc.find_exn cfg.edges block ~equal in
    let cfg = { cfg with blocks = List.Assoc.add cfg.blocks block is ~equal } in
    let cfg = List.fold succs ~init:cfg ~f:(rename_phi stacks' block) in
    let imms = List.filter nodes ~f:(fun b -> is_immediate doms block b) in
    List.fold imms ~init:cfg ~f:(fun acc imm -> rename_block imm acc stacks') in
  rename_block entry cfg stacks

(** [remove_uninit_phis args instr] removes phi-node reads from [instr] if they
    read from a block that does no initialize the variable in question.
    Instructions that are not phi-nodes are left untouched. *)
let remove_uninit_phis args = function
  | Bril.Phi (dest, a, l, dest') ->
    let zipped = List.zip_exn a l in
    let zipped = List.filter zipped ~f:(fun (a, l) -> String.contains a '.' || mem a args) in
    let a, l = List.unzip zipped in
    Bril.Phi (dest, a, l, dest')
  | i -> i

let not_single_phi = function
  | Bril.Phi (dest, [a], [l], dest') -> false
  | _ -> true

(** [ssa_of_instrs args instrs] is a modified version of [intrs] in SSA form.
    The transformation inserts an entry block at the head of the CFG in case
    there is a back-edge entering the original entry block, inserts empty
    phi-nodes, and renames variables to fill in the phi-node reads. As a
    post-processing pass, any phi-node reads from blocks that do not initialize
    the variable in question are removed. *)
let ssa_of_instrs (args : Bril.dest list) (instrs : Bril.instr list) : Bril.instr list =
  let cfg = Bril.to_blocks_and_cfg instrs in
  let entry = List.hd_exn cfg.order in
  let cfg, entry =
    let open Bril in
    if List.exists cfg.edges ~f:(fun (e, succs) -> mem entry succs)
    then
      { blocks = ("entry1", [Label "entry1"; Jmp entry ]) :: cfg.blocks;
        edges = ("entry1", [entry]) :: cfg.edges;
        order = "entry1" :: cfg.order; },
      "entry1"
    else cfg, entry in
  let doms = get_dominance_map cfg in
  let cfg = insert_phis args cfg doms in
  let cfg = rename_vars args cfg doms entry in
  let cfg = { cfg with blocks = List.map cfg.blocks
    ~f:(fun (b, is) -> b, List.map is ~f:(remove_uninit_phis (List.map args ~f:fst))) } in
  let blocks = List.map cfg.order ~f:(List.Assoc.find_exn cfg.blocks ~equal) in
  List.fold ~init:[] ~f:(@) blocks

let ssa_of_func (func : Bril.func) : Bril.func =
  { func with instrs = ssa_of_instrs func.args func.instrs }

let ssa_of_bril (bril : Bril.t) : Bril.t =
  { funcs = List.map (add_labels bril).funcs ~f:ssa_of_func }

let not_phi (instr : Bril.instr) : bool =
  match instr with
  | Phi _ -> false
  | _ -> true

let instrs_of_ssa (instrs : Bril.instr list) : Bril.instr list =
  let cfg = Bril.to_blocks_and_cfg instrs in
  let order = List.map cfg.blocks ~f:fst in
  let cfg = List.fold cfg.blocks ~init:cfg ~f:(fun cfg (b, is) ->
    List.fold is ~init:cfg ~f:(fun cfg i ->
      match i with
      | Phi(dest, args, ls, dest') ->
        let zipped = List.zip_exn ls args in
        List.fold zipped ~init:cfg ~f:(fun cfg (label, arg) ->
          let pred_is = List.Assoc.find_exn cfg.blocks label ~equal in
          let id_instr = Bril.Unary (dest, Bril.Id, arg) in
          let updated = match List.rev pred_is with 
            | Bril.Jmp x :: tl -> (Bril.Jmp x :: id_instr :: tl) |> List.rev
            | Bril.Br (a,b,c) :: tl -> (Bril.Br(a,b,c) :: id_instr :: tl) |> List.rev
            | tl -> (id_instr :: tl) |> List.rev in
          { cfg with blocks =
            List.Assoc.add cfg.blocks label updated ~equal } )
      | _ -> cfg )) in
  List.fold order ~init:[] ~f:(fun acc b -> acc @ List.Assoc.find_exn cfg.blocks b ~equal)
  |> List.filter ~f:not_phi

let func_of_ssa (func : Bril.func) : Bril.func =
  { func with instrs = instrs_of_ssa func.instrs }

let bril_of_ssa (bril : Bril.t) : Bril.t =
  { funcs = List.map (add_labels bril).funcs ~f:func_of_ssa }