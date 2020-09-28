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

let merge (v1 : cp_val) (v2 : cp_val) : cp_val = init_cp (* TODO *)

let mergel = List.fold ~init:init_cp ~f:merge

let transfer (is : Bril.instr list) (inv : cp_val) : Bril.instr list * cp_val =
  is, inv

let vals_equal (v1 : cp_val) (v2 : cp_val) : bool = false

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