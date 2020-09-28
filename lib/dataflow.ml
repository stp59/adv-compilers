open Core

type var_val =
  | Uninit
  | Const of Bril.const
  | Conflict

type block_val =
  | Reachable
  | Unreachable

type cp_val = {
  bv : block_val;
  vvs : (string * var_val) list;
}

type df_val = {
  inv : cp_val;
  outv : cp_val;
}

let init_cp : cp_val = {
  bv = Reachable;
  vvs = [];
}

let init : df_val = {
  inv = init_cp;
  outv = init_cp;
}

let empty l = List.length l |> Int.equal 0

let mem l v = List.exists l ~f:(fun x -> String.equal v x)

let merge_block v1 v2 =
  match v1, v2 with
  | Reachable, _ | _, Reachable -> Reachable
  | _, _ -> Unreachable

let merge_var v1 v2 =
  match v1, v2 with
  | Uninit, _ -> v2
  | _, Uninit -> v1
  | Conflict, _ | _, Conflict -> Conflict
  | Const c1, Const c2 ->
    if Bril.equal_const c1 c2 then Const c1 else Conflict

let merge (v1 : cp_val) (v2 : cp_val) : cp_val = {
  bv = merge_block v1.bv v2.bv;
  vvs = List.fold v2.vvs ~init:v1.vvs
    ~f:(fun acc (n, v) -> List.Assoc.add acc n
      (merge_var (List.Assoc.find acc n ~equal:String.equal
          |> Option.value_map ~default:v ~f:Fn.id) v) ~equal:String.equal);
}

let mergel = List.fold ~init:init_cp ~f:merge

let transfer (is : Bril.instr list) (inv : cp_val) : Bril.instr list * cp_val =
  is, inv (* TODO *)

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
  

let cp_worklist (blocks : (string * Bril.instr list) list)
    (edges : (string * string list) list) : (string * Bril.instr list) list =
  let equal = String.equal in
  let vals = List.map blocks ~f:(fun (b, _) -> b, init) in
  let wklst : string list = List.map ~f:fst blocks in
  let loop_body curr wklst vals blocks edges =
    let v = List.Assoc.find_exn vals curr ~equal in
    let preds =
      List.filter edges ~f:(fun (n, l) -> mem l curr)
      |> List.map ~f:fst in
    let inv = mergel (List.map preds ~f:(fun n -> (List.Assoc.find_exn vals n ~equal).outv)) in
    let b', outv = transfer (List.Assoc.find_exn blocks curr ~equal) inv in
    let wklst = if vals_equal outv v.outv then wklst else curr :: wklst in
    let vals =
      if empty b'
      then List.Assoc.remove vals curr ~equal
      else List.Assoc.add vals curr {inv; outv;} ~equal in
    let blocks =
      if empty b'
      then List.Assoc.remove blocks curr ~equal
      else List.Assoc.add blocks curr b' ~equal in
    let edges =
      if empty b'
      then List.Assoc.remove edges curr ~equal
      else edges in
    let edges =
      if empty b'
      then List.map edges ~f:(fun (n, l) -> n, List.filter l
        ~f:(fun m -> String.equal m curr))
      else edges in
    wklst, vals, blocks, edges in
  let rec main_loop (wklst, vals, blocks, edges) =
    match wklst with
    | [] -> wklst, vals, blocks, edges
    | n :: t -> main_loop (loop_body n t vals blocks edges) in
  let (_, _, blocks, _) = main_loop (wklst, vals, blocks, edges) in
  blocks

let cp_func (func : Bril.func) : Bril.func =
  let Bril.{ blocks; edges } = Bril.to_blocks_and_cfg func.instrs in
  let blocks' = cp_worklist blocks edges in
  let f acc (l, b) =
    List.Assoc.find blocks' l ~equal:String.equal
    |> Option.value_map ~default:acc ~f:(fun b' -> (l, b') :: acc) in
  let instrs' = List.fold blocks ~init:[] ~f
    |> List.map ~f:snd
    |> List.fold ~init:[] ~f:(@) in
  { func with instrs = instrs'; }

let cp (bril : Bril.t) : Bril.t =
  { funcs = List.map ~f:cp_func bril.funcs }