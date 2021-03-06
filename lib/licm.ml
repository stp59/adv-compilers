open Core
open Util

let fresh_label =
  let box = ref (-1) in
  fun () -> box := !box + 1; sprintf "licm.prehdr.%d" (!box)

module RDFramework = struct
  type var_def  = {
    block : string;
    idx : int;
  }

  (** Maps variables to lists of instructions that define them *)
  type v = (string * var_def list) list

  let var_defs_equal d1 d2 =
    equal d1.block d2.block && Int.equal d1.idx d2.idx

  let var_vals_equal v1 v2 =
    List.for_all v1
      ~f:(fun d1 -> List.exists v2 ~f:(fun d2 -> var_defs_equal d1 d2))
    && List.for_all v2
      ~f:(fun d2 -> List.exists v1 ~f:(fun d1 -> var_defs_equal d1 d2))

  let vals_equal v1 v2 =
    List.for_all v1
      ~f:(fun (var, v) -> List.Assoc.find_exn v2 var ~equal |> var_vals_equal v)
    && List.for_all v2
      ~f:(fun (var, v) -> List.Assoc.find_exn v1 var ~equal |> var_vals_equal v)

  let init (func : Bril.func) (cfg : Bril.cfg) =
    let args = List.map func.args ~f:fst in
    let vars = get_vars func.args cfg |> List.map ~f:fst in
    let entry = List.hd_exn cfg.order in
    let init = List.map vars
      ~f:(fun v -> v, if mem v args then [{block=entry; idx=(-1)}] else []) in
    List.map cfg.blocks ~f:(fun (b, is) -> b, Dataflow.{inv=init; outv=init; })

  let transfer (block : string) (instrs : Bril.instr list) (inv : v) =
    let f idx acc (i : Bril.instr) =
      match i with
      | Const ((n, _), _) | Binary ((n, _), _, _, _)
      | Unary ((n, _), _, _) | Call (Some (n, _), _, _)
      | Phi ((n, _), _, _, _) -> List.Assoc.add acc n idx ~equal
      | _ -> acc in
    let inv = List.filter inv ~f:(fun (v, _) -> not (defs_var v instrs)) in
    let gens = List.foldi instrs ~init:[] ~f
      |> List.map ~f:(fun (v, idx) -> v, [{block; idx}]) in
    instrs, inv @ gens

  let merge_vars v1 v2 =
    List.fold v1 ~init:v2 ~f:(fun acc d1 ->
      if List.exists acc ~f:(fun d2 -> equal d1.block d2.block)
      then acc else d1 :: acc)

  let merge v1 v2 =
    List.map v1 ~f:fst
    |> List.map ~f:(fun var -> var, merge_vars
      (List.Assoc.find_exn v1 var ~equal)
      (List.Assoc.find_exn v2 var ~equal))

  let mergel init vs =
    List.fold vs ~init ~f:merge

end

module RDAnalysis = Dataflow.MakeAnalysis(RDFramework)

type loop = {
  header : string;
  blocks : string list;
  pre_header : string;
  exits : string list;
}

(** [get_backedges cfg doms] is a list of ordered [string * string] pairs which
    represent backedges in the [cfg]. *)
let get_backedges (cfg : Bril.cfg) (doms : dominance_map) : (string * string) list =
  let edges = List.map cfg.edges ~f:(fun (n, es) -> List.map es ~f:(fun e -> n,e))
    |> List.fold ~init:[] ~f:(@) in
  List.filter edges ~f:(fun (b,a) -> List.Assoc.find_exn doms b ~equal |> mem a)

(** [get_loop cfg doms backedge] is a loop in the [cfg] generated around the [backedge]. *)
let get_loop (cfg: Bril.cfg) (doms: dominance_map) (backedge: string * string): loop =
  let exit, head = backedge in
  (* fprintf Out_channel.stdout "backedge: %s -> %s\n" exit head; *)
  let loop = {
    blocks = if equal exit head then [head] else[head; exit;];
    header = head;
    pre_header = "";
    exits = []
  } in
  let rec add_preds loop =
    let preds = loop.blocks
      |> List.filter ~f:(fun b -> equal b head |> not)
      |> List.map ~f:(fun b -> get_preds b cfg)
      |> List.fold ~init:[] ~f:(@) in
    let blocks = List.fold preds ~init:loop.blocks
      ~f:(fun acc p -> if mem p acc then acc else p :: acc) in
    if Int.equal (List.length blocks) (List.length loop.blocks)
    then loop
    else add_preds { loop with blocks = blocks; } in
  let loop = add_preds loop in
  { loop with exits =
      List.filter loop.blocks ~f:(fun b -> List.Assoc.find_exn cfg.edges b ~equal
        |> List.for_all ~f:(fun s -> mem s loop.blocks) |> not) }

(** [is_natural cfg loop] is [true] iff. the set of nodes given by [loop] only
    has one in-going edge according to the [cfg]. *)
let is_natural (cfg : Bril.cfg) (loop : loop) : bool =
  let preds = loop.blocks
    |> List.map ~f:(fun b -> get_preds b cfg)
    |> List.fold ~init:[] ~f:(@)
    |> List.filter ~f:(fun b -> not (mem b loop.blocks)) in
  let header_preds = get_preds loop.header cfg in
  List.for_all preds ~f:(fun p -> mem p header_preds) &&
  List.for_all preds ~f:(fun p -> List.Assoc.find_exn cfg.edges p ~equal
    |> List.for_all ~f:(fun s -> equal s loop.header || not (mem s loop.blocks)))

(** [change_jumps is before after] is [is] with every occurence of the
    label [before] in jump or branch instruction replaced with the label [after].*)
let change_jumps (is: Bril.instr list) (before: string) (after: string): Bril.instr list =
  let f = function
    | Bril.Jmp l -> if equal l before then Bril.Jmp after else Bril.Jmp l
    | Bril.Br (arg, l1, l2) ->
      let l1 = if equal l1 before then after else l1 in
      let l2 = if equal l2 before then after else l2 in
      Bril.Br (arg, l1, l2)
    | i -> i in
  List.map is ~f

let union (l1 : string list) (l2 : string list) : string list =
  List.fold l1 ~init:l2 ~f:(fun acc b -> if mem b acc then acc else b :: acc)

let merge_loops (l1 : loop) (l2 : loop) : loop = {
  blocks = union l1.blocks l2.blocks;
  header = l1.header;
  pre_header = l1.pre_header;
  exits = union l1.exits l2.exits;
}

let merge_sc_loops (acc : (string * loop) list)
    (idx, loop : string * loop) : (string * loop) list =
  let entry = List.find acc ~f:(fun (idx, l) -> equal loop.header l.header) in
  let entry = Option.map entry ~f:(fun (idx, l) -> idx, merge_loops loop l) in
  let idx, loop = Option.value_map entry ~default:(idx,loop) ~f:Fn.id in
  List.Assoc.add acc idx loop ~equal

(** [add_pre_headers (cfg, loops) (i, loop)] is a modified version of both the
    [cfg] and the indexed list of [loops] which adds proper pre-headers to the
    [i]th [loop] if one does not yet exist. *)
let add_pre_header (cfg, loops : Bril.cfg * (string * loop) list)
    (i : string) : Bril.cfg * (string * loop) list =
  let loop = List.Assoc.find_exn loops i ~equal in
  let header_preds = get_preds loop.header cfg
    |> List.filter ~f:(fun b -> mem b loop.blocks |> not) in
  if List.length header_preds |> Int.equal 1
  then begin
    (* print_endline "not inserting new block"; *)
    let loop = { loop with pre_header = List.hd_exn header_preds } in
    cfg, List.Assoc.add loops i loop ~equal end
  else begin
    (* print_endline "inserting new block"; *)
    let new_block = fresh_label () in
    let f acc b =
      if equal loop.header b
      then b :: new_block :: acc
      else b :: acc in
    let pre_header_code = [ Bril.Label (new_block); Bril.Jmp loop.header; ] in
    let order = List.fold cfg.order ~init:[] ~f |> List.rev in
    let blocks = List.Assoc.add cfg.blocks new_block pre_header_code ~equal in
    let f (b, is) =
      if mem b loop.blocks || equal b new_block then b, is
      else b, change_jumps is loop.header new_block in
    let blocks = List.map blocks ~f in
    let edges = Bril.update_edges blocks in
    let cfg = Bril.{ blocks; edges; order; } in
    let f (i, loop') =
      let blocks =
        if mem new_block loop'.blocks && not (equal new_block loop'.header)
        then new_block :: loop'.blocks
        else loop'.blocks in
      i, { loop with blocks = blocks; } in
    let loops = List.map loops ~f in
    let loop = { loop with pre_header = new_block; } in
    let loops = List.Assoc.add loops i loop ~equal in
    cfg, loops end

let tag_instr_lis (loop : loop) (rdefs : RDFramework.v) (block : string) (idx : int) (lis : (string * int list) list)
    (instr : Bril.instr) : RDFramework.v * bool =
  let var, args = match instr with
    | Label _ -> None, []
    | Const ((var, _), _) -> Some var, []
    | Binary ((var, _), _, a1, a2) -> Some var, [a1; a2]
    | Unary ((var, _), _, a) -> Some var, [a]
    | Jmp l -> None, []
    | Br (arg, _, _) -> None, [arg]
    | Call (Some (var, _), _, args) -> Some var, args
    | Call (None, _, args) -> None, args
    | Ret None -> None, []
    | Ret (Some a) -> None, [a]
    | Print args -> None, args
    | Nop -> None, []
    | Phi ((var, _), args, _, _) -> Some var, args in
  Option.value_map var ~default:rdefs
    ~f:(fun var -> List.Assoc.add rdefs var [{block; idx; }] ~equal),
  let f var = 
    (* fprintf Out_channel.stdout "Reaching definitions for block %s, variable %s are in blocks:\n" block var; *)
    (* List.iter (List.Assoc.find_exn rdefs var ~equal) ~f:(fun {block; idx} -> fprintf Out_channel.stdout "  %s\n" block); *)
    let defs = List.Assoc.find_exn rdefs var ~equal in 
    let all_out = List.for_all defs
      ~f:(fun {block; _} -> not (mem block loop.blocks)) in
    let only_one = List.length defs |> Int.equal 1 in
      all_out || (only_one &&
        List.exists lis ~f:(fun (b, is) -> equal b (List.hd_exn defs).block &&
          List.exists is ~f:(fun i -> Int.equal i (List.hd_exn defs).idx))) in
  (* if *)
    List.for_all args ~f
  (* then begin fprintf Out_channel.stdout "Tagging block %s, instr #%d as loop-invariant.\n" block idx; true end *)
  (* else begin fprintf Out_channel.stdout "Not tagging block %s, instr #%d as loop-invariant.\n" block idx; false end *)

let tag_block_lis (cfg : Bril.cfg) (loop : loop) (rdefs : (string * RDFramework.v Dataflow.df_val) list)
    (lis : (string * int list) list) (block : string) : (string * int list) list =
  (* fprintf Out_channel.stdout "Tagging loop-invariant code for loop block \"%s\".\n" block; *)
  let idxs = List.Assoc.find lis block ~equal
    |> Option.value_map ~default:[] ~f:Fn.id in
  let instrs = List.Assoc.find_exn cfg.blocks block ~equal in
  let block_rdefs = (List.Assoc.find_exn rdefs block ~equal).inv in
  let f idx (block_rdefs, is) instr =
    let block_rdefs, cond = tag_instr_lis loop block_rdefs block idx lis instr in
    block_rdefs, if cond then idx :: is else is in
  let _, new_idxs = List.foldi instrs ~init:(block_rdefs, []) ~f in
  let f acc i =
    if List.exists acc ~f:(Int.equal i)
    then acc
    else i :: acc in
  let idxs = List.fold new_idxs ~init:idxs ~f in
  List.Assoc.add lis block idxs ~equal

let same_idxs (idxs1 : int list) (idxs2 : int list) : bool =
  List.for_all idxs1 ~f:(fun i -> List.exists idxs2 ~f:(Int.equal i)) &&
  List.for_all idxs2 ~f:(fun i -> List.exists idxs1 ~f:(Int.equal i))

let lis_equal (lis1 : (string * int list) list) (lis2 : (string * int list) list) : bool =
  let f lis b =
    List.Assoc.find lis b ~equal |> Option.value_map ~default:[] ~f:Fn.id in
  List.for_all lis1 ~f:(fun (b, idxs) -> same_idxs idxs (f lis2 b)) &&
  List.for_all lis2 ~f:(fun (b, idxs) -> same_idxs idxs (f lis1 b))

(** [tag_lis cfg loop rdefs] is a list of mappings from blocks to lines numbers,
    each of which point to an instruction which is loop invariant with respect to
    the [cfg] and the given [loop]. *)
let tag_lis (cfg : Bril.cfg) (rdefs : (string * RDFramework.v Dataflow.df_val) list)
    (loop : loop) : (string * int list) list =
  (* fprintf Out_channel.stdout "Tagging loop-invariant code for loop with header \"%s\".\n" loop.header; *)
  let rec f acc =
    let acc' = List.fold loop.blocks ~init:acc ~f:(tag_block_lis cfg loop rdefs) in
    if lis_equal acc acc' then acc' else f acc' in
  f []

let has_effects (instr : Bril.instr) : bool =
  match instr with
  | Label _ | Binary (_, Div, _, _) | Binary (_, Fdiv, _, _) | Jmp _
  | Br (_, _, _) | Call (_, _, _) | Ret _ | Print _ -> true
  | Const (_, _) | Binary (_, _, _, _) | Unary (_, _, _)
  | Nop | Phi (_, _, _, _) -> false

let block_uses_var (cfg: Bril.cfg) (block: string) (var: string): bool =
  let f (defed, used) (instr : Bril.instr) = 
    let defed', used' = match instr with
    | Label _ | Jmp _ | Ret None | Nop ->
      false, false
    | Const ((d, _), _) -> equal var d, false
    | Binary ((d, _), _, arg1, arg2) ->
      equal var d, equal arg1 var || equal arg2 var
    | Unary ((d,_), _, arg) ->
      equal var d, equal arg var
    | Br (arg, _, _) | Ret (Some arg) ->
      false, equal arg var
    | Call (Some (d, _), _, args) | Phi ((d, _), args, _, _) ->
      equal var d, List.exists args ~f:(equal var)
    | Print args | Call (None, _, args) ->
      false, List.exists args ~f:(equal var) in
    (defed || defed'), not defed && (used || used') in
  let instrs = List.Assoc.find_exn cfg.blocks block ~equal in 
  List.fold instrs ~init:(false, false) ~f |> snd

let get_var (instr : Bril.instr) : string option =
  match instr with
  | Const ((var, _), _) | Binary ((var, _), _, _, _) | Unary ((var, _), _, _)
  | Call (Some (var, _), _, _) | Phi ((var, _), _, _, _) -> Some var
  | _ -> None

(** [is_safe cfg doms loop block idx] is [true] iff. the [idx]th intruction in
    the [block] is "safe" to move into the loop header. "Safe" instructions meet
    the following criteria:
      1) The instruction is guaranteed to have no side-effects
      2) The instruction dominates all uses of the variable defined
      3) There are no definitions of the same variable in the rest of the loop
      4) The instruction dominates all loop exits, or the variable is dead after
         the loop *)
let is_safe (cfg : Bril.cfg) (doms : dominance_map) (loop : loop)
    (rdefs : (string * RDFramework.v Dataflow.df_val) list) (block : string)
    (idx : int) : bool =
  (* print_endline "about to get instr"; *)
  let instr = List.nth_exn (List.Assoc.find_exn cfg.blocks block ~equal) idx in
  (* print_endline "got instr"; *)
  let var = get_var instr in
  (* let _print_cond = equal block "loop" && Option.equal equal var (Some "c") in *)
  let no_effects = not (has_effects instr) in
  (* let () = if no_effects && print_cond then print_endline "def has no effects" else () in *)
  let f (b, is) =
    let doms = List.Assoc.find_exn doms b ~equal |> mem block in
    (* print_endline "got doms"; *)
    (* fprintf Out_channel.stdout "Block %s dominates block %s\n" block b; *)
    let uses = Option.value_map var ~default:false ~f:(block_uses_var cfg b) in
    let reaches = match var with None -> false | Some var -> rdefs
      |> (fun x -> (List.Assoc.find_exn x b ~equal).inv)
      |> (fun x -> List.Assoc.find_exn x var ~equal)
      |> List.exists ~f:(fun RDFramework.{block=b; idx=i} -> Int.equal i idx && equal b block) in
    doms || not (uses && reaches) in
  (* print_endline "got reaches"; *)
  let doms_uses = List.for_all cfg.blocks ~f in
  (* let () = if doms_uses && print_cond then print_endline "def has doms uses" else () in *)
  (* fprintf Out_channel.stdout "Blocks in the loop are: \n"; *)
  (* List.iter loop.blocks ~f:(fun b -> fprintf Out_channel.stdout "  %s\n" b); *)
  let no_redefs = loop.blocks
    |> List.map ~f:(List.Assoc.find_exn cfg.blocks ~equal)
    |> List.fold ~init:[] ~f:(@)
    |> List.filter ~f:(fun i -> Option.value_map var ~default:false ~f:(fun v -> defs_var v [i]))
    |> List.length
    |> (fun l ->
      (* Option.value_map var ~default:() ~f:(fun v -> fprintf Out_channel.stdout "Num defs for %s is: %d\n" v l); *)
      (>=) 1 l) in
  (* print_endline "got no_rdefs"; *)
  let doms_exits = List.for_all loop.exits
    ~f:(fun exit -> List.Assoc.find_exn doms exit ~equal |> mem block) in
  (* print_endline "got doms_exits"; *)
  let f (b, _) =
    let rdefs = (List.Assoc.find_exn rdefs b ~equal).inv in
    (* print_endline "got rdefs for block"; *)
    let rdefs = Option.value_map var ~default:[]
      ~f:(fun var -> List.Assoc.find_exn rdefs var ~equal) in
    (* print_endline "got rdefs for var"; *)
    List.exists rdefs ~f:(fun {block=b; _} -> equal block b) in
  let dead_after = cfg.blocks
    |> List.filter ~f:(fun (b, _) -> not (mem b loop.blocks) )
    |> List.filter ~f
    |> List.map ~f:fst
    |> List.exists ~f:(fun b -> Option.value_map var ~default:false ~f:(block_uses_var cfg b)) in
  (* print_endline "got dead after"; *)
  no_effects && doms_uses && no_redefs && (doms_exits || dead_after)

let move_code (cfg : Bril.cfg) (doms : dominance_map) (loop : loop)
    (li : (string * int list) list) : Bril.cfg =
  (* print_endline "moving code"; *)
  let is_tagged b (i, instr) =
    (* print_endline "about to check is tagged"; *)
    (* let ans =  *)
      List.Assoc.find_exn li b ~equal |> List.exists ~f:(Int.equal i) in
    (* print_endline "is tagged fine"; ans in *)
  let f (b, instrs) = 
    let idx_instrs = List.mapi instrs ~f:(fun i instr -> i, instr) in
    let idx_loop_inv, idx_loop_v = List.partition_tf idx_instrs ~f:(is_tagged b) in
    b, (List.map idx_loop_inv ~f:snd, List.map idx_loop_v ~f:snd) in
  let loop_inv, loop_v =
    List.map loop.blocks ~f:(fun b -> b, List.Assoc.find_exn cfg.blocks b ~equal)
    |> List.map ~f
    |> List.map ~f:(fun (b, (is1, is2)) -> (b, is1), (b, is2))
    |> List.unzip in
  (* print_endline "got loop_inv and loop_v"; *)
  let compare (a, _) (b, _) =
    (* print_endline "doing compare"; *)
    let adomsb = List.Assoc.find_exn doms b ~equal |> mem a in
    let bdomsa = List.Assoc.find_exn doms a ~equal |> mem b in
    (* print_endline "compare successful"; *)
    if adomsb then -1
    else if bdomsa then 1
    else 0 in
  let loop_inv = List.sort loop_inv ~compare
    |> List.fold ~init:[] ~f:(fun acc (_, is) -> acc @ is) in
  (* print_endline "getting pre_header_code"; *)
  (* fprintf Out_channel.stdout "pre-header block name is %s\n" loop.pre_header; *)
  let pre_header_code = List.Assoc.find_exn cfg.blocks loop.pre_header ~equal in
  (* print_endline "got pre_header_code"; *)
  let loop_inv = match List.rev pre_header_code with
    | Jmp l :: tl -> (List.rev tl) @ loop_inv @ [Jmp l]
    | Br (arg, l1, l2) :: tl -> (List.rev tl) @ loop_inv @ [Br (arg, l1, l2)]
    | tl -> (List.rev tl) @ loop_inv in
  let f (acc : Bril.cfg) (b, is) =
    { acc with blocks = List.Assoc.add acc.blocks b is ~equal } in
  let cfg = List.fold loop_v ~init:cfg ~f in
  { cfg with blocks = List.Assoc.add cfg.blocks loop.pre_header loop_inv ~equal }

(** [move_func_code func] is a modified verision of [func] in which all loop-
    invariant code is moved to the preheader of every natural loop (and
    pre-headers are inserted as needed). *)
let move_func_code (func : Bril.func) : Bril.func =
  let cfg = Bril.to_blocks_and_cfg func.instrs in
  let doms = get_dominance_map cfg in
  let backedges = get_backedges cfg doms in
  (* print_endline "got backedges"; *)
  let loops = List.map backedges ~f:(get_loop cfg doms) in
  (* print_endline "got loops"; *)
  let loops = List.filter loops ~f:(is_natural cfg) in
  (* print_endline "filtered for natural"; *)
  let idx_loops = List.init (List.length loops) ~f:string_of_int in
  let zipped = List.zip_exn idx_loops loops in
  let zipped = List.fold zipped ~init:[] ~f:merge_sc_loops in
  let idx_loops = List.map zipped ~f:fst in
  let cfg, loops = List.fold idx_loops ~init:(cfg, zipped) ~f:add_pre_header in
  (* print_endline "added pre_headers"; *)
  let loops = List.map loops ~f:snd in
  (* fprintf Out_channel.stdout "Num loops: %d\n" (List.length loops); *)
  let doms = get_dominance_map cfg in
  (* print_endline "got dominance map"; *)
  let move_loop_code cfg loop =
    let vals, _ = RDAnalysis.worklist func cfg in
    (* print_endline "got rdefs"; *)
    let lis = tag_lis cfg vals loop in
    (* print_endline "tagged lis"; *)
    let lis = List.map lis ~f:(fun (b, is) -> b, List.filter is
      ~f:(fun i -> is_safe cfg doms loop vals b i)) in
    (* print_endline "filtered for safe"; *)
    move_code cfg doms loop lis in
  let cfg = List.fold loops ~init:cfg ~f:move_loop_code in
  { func with instrs = cfg.order
    |> List.map ~f:(fun b -> List.Assoc.find_exn cfg.blocks b ~equal)
    |> List.fold ~init:[] ~f:(@) }

let move_code (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:move_func_code }
