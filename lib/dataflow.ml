open Core
open Util

type cp_var_val =
  | Uninit
  | Const of Bril.const
  | Conflict

type cp_block_val =
  | Reachable
  | Unreachable

type cp_val = {
  bv : cp_block_val;
  vvs : (string * cp_var_val) list;
}

type 'v df_val = {
  inv : 'v;
  outv : 'v;
}

let pre_cp_init : cp_val = {
  bv = Reachable;
  vvs = [];
}

let cp_init : cp_val df_val = {
  inv = pre_cp_init;
  outv = pre_cp_init;
}

let cp_init (func : Bril.func) (cfg : Bril.cfg) : (string * cp_val df_val) list =
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
    if Bril.equal_const c1 c2 then Const c1 else (
      Conflict)

let cp_merge (v1 : cp_val) (v2 : cp_val) : cp_val = {
  bv = merge_block v1.bv v2.bv;
  vvs = List.fold v2.vvs ~init:v1.vvs
    ~f:(fun acc (n, v) -> List.Assoc.add acc n
      (merge_var (List.Assoc.find acc n ~equal:String.equal
        |> Option.value_map ~default:v ~f:Fn.id) v) ~equal:String.equal);
}

let cp_mergel = List.fold ~init:pre_cp_init ~f:(cp_merge)

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

let cp_transfer (is : Bril.instr list) (inv : cp_val) : Bril.instr list * cp_val =
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
      let varg =
        List.Assoc.find v.vvs arg ~equal
        |> Option.value_map ~default:Uninit ~f:Fn.id in
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

let vals_equal (v1 : cp_val) (v2 : cp_val) : bool =
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

let worklist (cfg : Bril.cfg) ~init:init ~transfer:transfer
    ~merge:mergel : (string * 'v) list * Bril.cfg =
  let equal = String.equal in
  let blocks = cfg.blocks in
  let wklst : string list = List.map ~f:fst blocks in
  let loop_body curr wklst vals (cfg : Bril.cfg) : string list * (string * 'v) list * Bril.cfg =
    let blocks = cfg.blocks in 
    let edges = cfg.edges in
    let v = List.Assoc.find_exn vals curr ~equal in
    let preds = get_preds curr cfg in
    let inv = mergel (List.map preds ~f:(fun n -> (List.Assoc.find_exn vals n ~equal).outv)) in
    let b', outv = transfer (List.Assoc.find_exn blocks curr ~equal) inv in
    let wklst =
      if vals_equal outv v.outv
      then wklst
      else (List.Assoc.find edges curr ~equal
        |> Option.value_map ~default:[] ~f:Fn.id) @ wklst in
    let vals = List.Assoc.add vals curr {inv; outv;} ~equal in
    let blocks = List.Assoc.add blocks curr b' ~equal in
    let edges = Bril.update_edges blocks in
    wklst, vals, Bril.{ blocks; edges; } in
  let rec main_loop (wklst, vals, cfg) =
    match wklst with
    | [] -> wklst, vals, cfg
    | n :: t -> main_loop (loop_body n t vals cfg) in
  let (_, vals, cfg) = main_loop (wklst, init, cfg) in
  vals, cfg

let cp_func (func : Bril.func) : Bril.func =
  let cfg = Bril.to_blocks_and_cfg func.instrs in
  let order = List.map cfg.blocks ~f:fst in
  let _, cfg = worklist cfg ~init:(cp_init func cfg) ~transfer:cp_transfer ~merge:cp_mergel in
  let instrs' = List.map order ~f:(List.Assoc.find_exn cfg.blocks ~equal:String.equal)
    |> List.fold ~init:[] ~f:(@) in
  { func with instrs = instrs'; }

let cp (bril : Bril.t) : Bril.t =
  { funcs = List.map ~f:cp_func bril.funcs }