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

let init : cp_val = {
  bv = Reachable;
  vvs = [];
}

let cp_worklist (blocks : (string * Bril.instr list) list)
    (edges : (string * string list) list) : (string * Bril.instr list) list =
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