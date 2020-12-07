open Core
open Util

type 'v df_val = {
  inv : 'v;
  outv : 'v;
}

module type Framework = sig
  type v
  
  val vals_equal : v -> v -> bool

  val init : Bril.func -> Bril.cfg -> (string * v df_val) list

  val transfer : string -> Bril.instr list -> v -> Bril.instr list * v

  val mergel : v -> v list -> v

end

module MakeAnalysis (F : Framework) = struct

  let worklist (func : Bril.func) (cfg : Bril.cfg) : (string * F.v df_val) list * Bril.cfg =
    let equal = String.equal in
    let blocks = cfg.blocks in
    let order = cfg.order in
    let entry = List.hd_exn order in
    let wklst = List.map ~f:fst blocks in
    let init = F.init func cfg in
    let mergel = F.mergel (init |> List.hd_exn |> snd).inv in
    let loop_body curr wklst (vals : (string * 'v df_val) list) (acc_cfg : Bril.cfg) : string list * (string * 'v df_val) list * Bril.cfg =
      let edges = acc_cfg.edges in
      let blocks_tmp = List.map acc_cfg.order ~f:(fun b -> b, List.Assoc.find_exn acc_cfg.blocks b ~equal) in
      let edges_tmp = Bril.update_edges blocks_tmp in
      let acc_cfg_tmp = Bril.{ blocks = blocks_tmp; edges = edges_tmp; order; } in
      let v = List.Assoc.find_exn vals curr ~equal in
      let preds = get_preds curr acc_cfg in
      let preds = List.filter preds ~f:(fun p -> is_reachable acc_cfg_tmp entry p) in
      let inv = mergel (List.map preds ~f:(fun n -> (List.Assoc.find_exn vals n ~equal).outv)) in
      let b', outv = F.transfer curr (List.Assoc.find_exn cfg.blocks curr ~equal) inv in
      let wklst =
        if F.vals_equal outv v.outv
        then wklst
        else ((List.Assoc.find_exn edges curr ~equal)
          |> List.filter ~f:(fun n -> not (mem n wklst))) @ wklst in
      let vals = List.Assoc.add vals curr {inv; outv;} ~equal in
      let blocks = List.Assoc.add acc_cfg.blocks curr b' ~equal in
      let blocks = List.map acc_cfg.order ~f:(fun b -> b, List.Assoc.find_exn blocks b ~equal) in
      let acc_cfg = Bril.{ blocks; edges; order; } in
      wklst, vals, acc_cfg in
    let rec main_loop (wklst, vals, cfg) =
      match wklst with
      | [] -> wklst, vals, cfg
      | n :: t -> main_loop (loop_body n t vals cfg) in
    let (_, vals, cfg) = main_loop (wklst, init, cfg) in
    vals, cfg

end

module CPFramework = struct

  type var_val =
    | Uninit
    | Const of Bril.const
    | Conflict

  type block_val =
    | Reachable
    | Unreachable

  type v = {
    bv : block_val;
    vvs : (string * var_val) list;
  }

  let init (func : Bril.func) (cfg : Bril.cfg) : (string * v df_val) list =
    let args = List.map func.args ~f:fst in
    let vars = get_vars func.args cfg |> List.map ~f:fst in
    let init = List.map vars ~f:(fun v -> v, if mem v args then Conflict else Uninit) in
    let init = { bv = Reachable; vvs = init } in
    List.map cfg.blocks ~f:(fun (b,_) -> b, { inv = init; outv = init; })

  let merge_block v1 v2 =
    match v1, v2 with
    | Reachable, _ | _, Reachable -> Reachable
    | _, _ -> Unreachable

  let merge_var v1 v2 =
    match v1, v2 with
    | Uninit, v | v, Uninit -> v
    | Conflict, _ | _, Conflict -> Conflict
    | Const c1, Const c2 ->
      if Bril.equal_const c1 c2 then Const c1 else Conflict

  let merge (v1 : v) (v2 : v) : v = {
    bv = merge_block v1.bv v2.bv;
    vvs = List.map v2.vvs ~f:fst
      |> List.map ~f:(fun v -> v, merge_var (List.Assoc.find_exn v1.vvs v ~equal)
        (List.Assoc.find_exn v2.vvs v ~equal));
  }

  let mergel init = List.fold ~init:init ~f:(merge)

  let symb_binop op v1 v2 =
    match v1, v2 with
    | Uninit, _ | _, Uninit -> Uninit
    | Conflict, _ | _, Conflict -> Conflict
    | Const (Bool b1), Const (Bool b2) ->
      begin match op with
        | Bril.And -> Const (Bool (b1 && b2))
        | Bril.Or -> Const (Bool (b1 || b2))
        | _ -> Conflict end
    | Const (Int i1), Const (Int i2) ->
      begin match op with
        | Add -> Const (Int (i1 + i2))
        | Mul -> Const (Int (i1 * i2))
        | Sub -> Const (Int (i1 - i2))
        | Div -> Const (Int (i1 / i2))
        | Eq -> Const (Bool (Int.equal i1 i2))
        | Lt -> Const (Bool (i1 < i2))
        | Gt -> Const (Bool (i1 > i2))
        | Le -> Const (Bool (i1 <= i2))
        | Ge -> Const (Bool (i1 >= i2))
        | _ -> Conflict end
    | Const (Float f1), Const (Float f2) ->
      begin match op with
        | Fadd -> Const (Float (f1 +. f2))
        | Fmul -> Const (Float (f1 *. f2))
        | Fsub -> Const (Float (f1 -. f2))
        | Fdiv -> Const (Float (f1 /. f2))
        | _ -> Conflict end
    | _ -> Conflict

  let symb_unop op v =
    match v with
    | Uninit | Conflict -> v
    | Const (Bool b) ->
      begin match op with
        | Bril.Not -> Const (Bool (not b))
        | Bril.Id -> Const (Bool b) end
    | Const c ->
      begin match op with
        | Bril.Id -> Const c
        | _ -> Conflict end

  let transfer (block : string) (is : Bril.instr list) (inv : v) : Bril.instr list * v =
    let equal = String.equal in
    let f (acc, v) i =
      match i with
      | Bril.Label l -> i :: acc, v
      | Bril.Const ((n, _), c) ->
        i :: acc, { v with vvs = List.Assoc.add v.vvs n (Const c) ~equal }
      | Binary ((n, t), op, n1, n2) ->
        let v1 =
          List.Assoc.find v.vvs n1 ~equal
          |> Option.value_map ~default:Uninit ~f:Fn.id in
        let v2 =
          List.Assoc.find v.vvs n2 ~equal
          |> Option.value_map ~default:Uninit ~f:Fn.id in
        let v0 = symb_binop op v1 v2 in
        let v = { v with vvs = List.Assoc.add v.vvs n v0 ~equal } in
        begin match v0 with
          | Uninit | Conflict -> i :: acc, v
          | Const c -> Const ((n, t), c) :: acc, v end
      | Unary ((n, t), op, n1) ->
        let v1 =
          List.Assoc.find v.vvs n1 ~equal
          |> Option.value_map ~default:Uninit ~f:Fn.id in
        let v0 = symb_unop op v1 in
        let v = { v with vvs = List.Assoc.add v.vvs n v0 ~equal } in
        begin match v0 with
          | Uninit | Conflict -> i :: acc, v
          | Const c -> Const ((n, t), c) :: acc, v end
      | Jmp l -> i :: acc, v
      | Br (arg, l1, l2) ->
        let varg = List.Assoc.find_exn v.vvs arg ~equal in
        begin match varg with
          | Uninit | Conflict -> i :: acc, v
          | Const (Bool true) -> Jmp l1 :: acc, v
          | Const (Bool false) -> Jmp l2 :: acc, v
          | _ -> failwith "malformed branch" end
      | Call (Some (n, t), _, _) ->
        i :: acc, {v with vvs = List.Assoc.add v.vvs n Conflict ~equal }
      | Call (None, _, _) -> i :: acc, v
      | Ret _ -> i :: acc, v
      | Print _ -> i :: acc, v
      | Nop -> i :: acc, v
      | Phi _ -> failwith "phi node cp dataflow unsupported" in
    let is', outv = List.fold is ~init:([], inv) ~f in
    List.rev is', outv

  let var_vals_equal v1 v2 =
    match v1, v2 with
    | Uninit, Uninit | Conflict, Conflict -> true
    | Const c1, Const c2 -> Bril.equal_const c1 c2
    | _ -> false

  let is_uninit v =
    match v with
    | Uninit -> true 
    | _ -> false

  let vals_equal (v1 : v) (v2 : v) : bool =
    let bveq = match v1.bv, v2.bv with
      | Reachable, Reachable | Unreachable, Unreachable -> true
      | _ -> false in
    let vvseq = List.for_all v1.vvs
      ~f:(fun (n, v) -> List.Assoc.find v2.vvs n ~equal:String.equal
        |> Option.value_map ~default:(is_uninit v) ~f:(var_vals_equal v)) &&
      List.for_all v2.vvs
        ~f:(fun (n, v) -> List.Assoc.find v1.vvs n ~equal:String.equal
          |> Option.value_map ~default:(is_uninit v) ~f:(var_vals_equal v)) in
    bveq && vvseq

end

module CPAnalysis = MakeAnalysis(CPFramework)

let cp_func (func : Bril.func) : Bril.func =
  let cfg = Bril.to_blocks_and_cfg func.instrs in
  let _, cfg = CPAnalysis.worklist func cfg in
  let instrs' = List.map cfg.order ~f:(List.Assoc.find_exn cfg.blocks ~equal:String.equal)
    |> List.fold ~init:[] ~f:(@) in
  { func with instrs = instrs'; }

let cp (bril : Bril.t) : Bril.t =
  { funcs = List.map ~f:cp_func bril.funcs }