open Core
open Util

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

(** [get_backedges cfg] is a list of ordered [string * string] pairs which
    represent backedges in the [cfg]. *)
let get_backedges (cfg : Bril.cfg) : (string * string) list =
  [] (* TODO *)

(** [get_loops cfg doms backedge] is a loop in the [cfg] generated around the
    [backedge] in the cfg. *)
let get_loop (cfg : Bril.cfg) (doms : dominance_map) (backedge : string * string) : loop =
  { blocks = []; header = ""; pre_header = ""; exits = []; } (* TODO *)

(** [is_natural cfg loop] is [true] iff. the set of nodes given by [loop] only
    has one in-going edge according to the [cfg]. *)
let is_natural (cfg : Bril.cfg) (loop : loop) : bool =
  false (* TODO *)

(** [add_pre_headers cfg loops] is a modified version of both the [cfg] and the
    list of [loops] which adds proper pre-headers to each loop in [loops] where
    one does not exist. *)
let add_pre_headers (cfg : Bril.cfg) (loops : loop list) : Bril.cfg * loop list =
  cfg, loops (* TODO *)

(** [tag_lis cfg loop rdefs] is a list of mappings from blocks to lines numbers,
    each of which point to an instruction which is loop invariant with respect to
    the [cfg] and the given [loop]. *)
let tag_lis (cfg : Bril.cfg) (rdefs : (string * RDFramework.v Dataflow.df_val) list)
    (loop : loop) : (string * int list) list =
  [] (* TODO *)

(** [is_safe cfg doms loop block idx] is [true] iff. the [idx]th intruction in
    the [block] is "safe" to move into the loop header. "Safe" instructions meet
    the following criteria:
      1) The instruction is guaranteed to have no side-effects
      2) The instruction dominates all uses of the variable defined
      3) There are no definitions of the same variable in the rest of the loop
      4) The instruction dominates all loop exits, or the variable is dead after
         the loop *)
let is_safe (cfg : Bril.cfg) (doms : dominance_map) (loop : loop)
    (block : string) (idx : int) : bool =
  false (* TODO *)

let move_code (cfg : Bril.cfg) (loop : loop) (li : (string * int list) list) : Bril.cfg =
  cfg (* TODO *)

(** [move_func_code func] is a modified verision of [func] in which all loop-
    invariant code is moved to the preheader of every natural loop (and
    pre-headers are inserted as needed). *)
let move_func_code (func : Bril.func) : Bril.func =
  let cfg = Bril.to_blocks_and_cfg func.instrs in
  let backedges = get_backedges cfg in
  let doms = get_dominance_map cfg in
  let loops = List.map backedges ~f:(get_loop cfg doms) in
  let loops = List.filter loops ~f:(is_natural cfg) in
  let cfg, loops = add_pre_headers cfg loops in
  let doms = get_dominance_map cfg in
  let vals, _ = RDAnalysis.worklist func cfg in
  let lis = List.map loops ~f:(tag_lis cfg vals) in
  let f loop li =
    List.map li ~f:(fun (b, is) -> b, List.filter is
      ~f:(fun i -> is_safe cfg doms loop b i)) in
  let lis = List.map2_exn loops lis ~f in 
  let cfg = List.fold2_exn loops lis ~init:cfg~f:move_code in
  { func with instrs = cfg.order
    |> List.map ~f:(fun b -> List.Assoc.find_exn cfg.blocks b ~equal)
    |> List.fold ~init:[] ~f:(@) }

let move_code (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:move_func_code }