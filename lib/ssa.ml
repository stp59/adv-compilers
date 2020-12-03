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

(** will map nodes to their dominators*)
let get_dominance_map (cfg : Bril.cfg) : dominance_map =
  (* print_endline "entry successors are: "; *)
  (* List.iter (List.Assoc.find_exn cfg.edges "here" ~equal) ~f:(fun x -> print_endline ("\t"^ x)); *)
  let nodes = List.map ~f:fst cfg.blocks in
  let init = List.map ~f:(fun v -> v, nodes) nodes in
  let rec f acc =
    let update acc v =
      (* print_endline v; *)
      let preds = get_preds v cfg in
      (* print_endline (string_of_int (List.length preds)); *)
      (* List.iter preds ~f:(print_endline); *)
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
    (* List.iter nodes ~f:(fun v -> List.Assoc.find_exn acc' v ~equal |> List.length |> string_of_int |> print_endline; *)
      (* List.Assoc.find_exn acc v ~equal |> List.length |> string_of_int |> print_endline); *)
    let changed = List.for_all nodes
      ~f:(fun v -> Int.equal (List.Assoc.find_exn acc' v ~equal |> List.length)
        (List.Assoc.find_exn acc v ~equal |> List.length)) in
    if changed then f acc' else acc' in
  f init

let strictly_dominates (doms : dominance_map) (a : string) (b : string) : bool =
  let bdoms = List.Assoc.find_exn doms b ~equal in
  mem a bdoms && not (equal a b)

let is_immediate (doms : dominance_map) (a : string) (b : string) : bool =
  (* print_endline ("checking if " ^ a ^ " immediately dominates " ^ b); *)
  let nodes = List.map doms ~f:fst in
  let bdoms = List.Assoc.find_exn doms b ~equal in
  let adomsb = mem a bdoms && not (equal a b) in
  (* let () = if adomsb then print_endline (a ^ " dominates " ^ b) else () in *)
  let f n =
    let ndomsb = strictly_dominates doms n b in
    let adomsn = strictly_dominates doms a n in
    (* let () = if adomsn && ndomsb then print_endline (n ^ " is intermediary between " ^ a ^ " and " ^ b) else () in *)
    adomsn && ndomsb in
    (* if ndomsb then adomsn else true in *)
    (* not (ndomsb && adomsn) in *)
  let cond = List.exists nodes ~f in
  (* let () = if cond then print_endline "exists intermediary as above" else print_endline "there is no intermediary" in *)
  adomsb && not cond

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
  let bpreds = get_preds b cfg in
  let bdoms = List.Assoc.find_exn doms b ~equal in
  let adomsb = mem a bdoms in
  let adoms_predb =
    List.exists bpreds ~f:(fun n -> List.Assoc.find_exn doms n ~equal |> mem a) in
  (* (if adomsb then print_endline (a ^ " dominates " ^ b) else ()); *)
  if (not adomsb) && adoms_predb
  then true 
    (* (print_endline (b ^ " is in the frontier of " ^ a); true) *)
  else false

let get_frontiers (cfg : Bril.cfg) (doms : dominance_map) : dominance_map =
  (* print_endline "getting frontier nodes"; *)
  let nodes = List.map cfg.blocks ~f:fst in
  let f n = n, List.filter nodes ~f:(fun v -> is_frontier cfg doms n v) in
  List.map nodes ~f

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

let defs_var (v : string) (instrs : Bril.instr list) : bool =
  let f instr =
    match instr with
    | Bril.Const ((dest, _), _) | Bril.Binary ((dest, _), _, _, _)
    | Bril.Unary ((dest, _), _, _) | Bril.Call (Some (dest, _), _, _)
    | Bril.Phi ((dest, _), _, _, _) -> equal dest v
    | _ -> false in
  List.exists instrs ~f

let get_var_defs (v : string) args (cfg : Bril.cfg) : string list =
  let nodes = List.map cfg.blocks ~f:fst in
  let entry = List.hd_exn nodes in
  (* print_endline ("\tentry: " ^ entry); *)
  let is_arg = List.exists args ~f:(fun (x,_) -> equal x v) in
  List.filter nodes
    ~f:(fun n -> (List.Assoc.find_exn cfg.blocks n ~equal |> defs_var v) || (is_arg && equal n entry))

let insert_phis (args : Bril.dest list) (cfg : Bril.cfg) doms : Bril.cfg =
  let vars = get_vars args cfg in
  (* let cfg = Bril.to_blocks_and_cfg instrs in *)
  (* let doms = get_dominance_map cfg in *)
  (* let _x = dominance_tree cfg doms in *)
  let fronts = get_frontiers cfg doms in
  List.fold vars ~init:cfg ~f:(fun cfg (var, t) ->
    (* print_endline var; *)
    let defs = get_var_defs var args cfg in
    List.fold defs ~init:cfg ~f:(fun cfg def ->
      (* print_endline ("\t" ^ def); *)
      let deffronts = List.Assoc.find_exn fronts def ~equal in
      List.fold deffronts ~init:cfg ~f:(fun cfg front ->
        (* print_endline ("\t" ^ front); *)
        let blck = List.Assoc.find_exn cfg.blocks front ~equal in
        let blck' = match blck with
          | Label _ :: Phi ((dest, t), _, _, _) :: _ when (equal dest var) -> blck
          | Label l :: tl -> Label l :: Phi ((var, t), [], [], (var, t)) :: tl
          | _ -> Phi ((var, t), [], [], (var, t)) :: blck in
        { cfg with blocks = List.Assoc.add cfg.blocks front blck' ~equal })))
  (* List.fold cfg'.blocks ~init:[] ~f:(fun acc (_, is) -> is @ acc) *)

let rename_vars (args : Bril.dest list) (cfg : Bril.cfg) doms entry : Bril.cfg =
  (* print_endline "renaming vars"; *)
  (* let cfg = Bril.to_blocks_and_cfg instrs in *)
  (* print_endline "got cfg"; *)
  (* let doms = get_dominance_map cfg in *)
  (* print_endline "got dominance map"; *)
  let nodes = List.map cfg.blocks ~f:fst in
  let vars = get_vars args cfg |> List.map ~f:fst in
  (* print_endline "got vars"; *)
  let stacks = List.map vars ~f:(fun v -> v, [v]) in
  let counters = List.map vars ~f:(fun v -> v, let box = ref (-1) in fun () -> box := !box + 1; !box) in
  (* let entry = List.hd_exn nodes in *)
  (* print_endline "got entry"; *)
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
      (* print_endline "renaming phi"; *)
      (* print_endline v; *)
      let fresh = v ^ "." ^ (List.Assoc.find_exn counters v ~equal () |> string_of_int) in
      (* print_endline fresh; *)
      List.Assoc.add stack v ~equal (fresh :: List.Assoc.find_exn stack v ~equal),
      (* (print_endline ("adding phi node with dest " ^ fresh); *)
      Phi ((fresh, t), args, ls, (v', t')) in
  let rename_phi stacks block (cfg : Bril.cfg) succ =
    let is = List.Assoc.find_exn cfg.blocks succ ~equal in
    let f i =
      match i with
      | Bril.Phi ((v, t), args, ls, (v', t')) ->
        Bril.Phi ((v, t), (List.Assoc.find_exn stacks v' ~equal |> List.hd_exn) :: args, block :: ls, (v', t'))
      | _ -> i in
    let is = List.map is ~f in
    { cfg with blocks = List.Assoc.add cfg.blocks succ is ~equal } in
  let rec rename_block block (cfg : Bril.cfg) stacks =
    (* print_endline ("renaming block: " ^ block); *)
    let is = List.Assoc.find_exn cfg.blocks block ~equal in
    (* print_endline "got is"; *)
    (* let () = failwith "end" in *)
    let (stacks', is) = List.fold_map is ~init:stacks ~f:rename_instr in
    let succs = List.Assoc.find_exn cfg.edges block ~equal in
    (* print_endline "got succs"; *)
    let cfg = { cfg with blocks = List.Assoc.add cfg.blocks block is ~equal } in
    (* print_endline "added is to cfg"; *)
    (* let () = failwith "end" in *)
    let cfg = List.fold succs ~init:cfg ~f:(rename_phi stacks' block) in
    (* print_endline "renamed phis"; *)
    let imms = List.filter nodes ~f:(fun b -> is_immediate doms block b) in
    (* print_endline ("immediately dominated are: "); *)
    (* List.iter imms ~f:(fun imm -> print_endline ("\t" ^ imm)); *)
    (* let () = failwith "end" in *)
    List.fold imms ~init:cfg ~f:(fun acc imm -> rename_block imm acc stacks') in
  (* print_endline ("entry: " ^ entry); *)
  rename_block entry cfg stacks

let ssa_of_instrs (args : Bril.dest list) (instrs : Bril.instr list) : Bril.instr list =
  let cfg = Bril.to_blocks_and_cfg instrs in
  let order = cfg.blocks |> List.map ~f:fst in
  let entry = List.hd_exn order in
  let doms = get_dominance_map cfg in
  (* let () = failwith "end" in *)
  let cfg = insert_phis args cfg doms in
  (* let () = failwith "end" in *)
  let cfg = rename_vars args cfg doms entry in
  let blocks = List.map order ~f:(List.Assoc.find_exn cfg.blocks ~equal) in
  List.fold ~init:[] ~f:(@) blocks

let ssa_of_func (func : Bril.func) : Bril.func =
  { func with instrs = ssa_of_instrs func.args func.instrs }

let ssa_of_bril (bril : Bril.t) : Bril.t =
  { funcs = List.map (add_labels bril).funcs ~f:ssa_of_func }

let bril_of_ssa (bril : Bril.t) : Bril.t =
  bril (* TODO *)