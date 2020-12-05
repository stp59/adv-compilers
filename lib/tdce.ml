open Core
open Util

let rec elim_dead_block (instrs : Bril.instr list) : Bril.instr list =
  let equal = String.equal in
  let f (i : int) (dels, defs : int list * (string * int) list) (instr : Bril.instr) =
    match instr with
    | Label _ -> dels, defs
    | Const ((dest, _), _) ->
      (if List.Assoc.mem defs dest ~equal
      then List.Assoc.find_exn defs dest ~equal :: dels else dels),
      List.Assoc.add defs dest i ~equal
    | Binary ((dest, _), _, arg0, arg1) ->
      let defs = List.fold [arg0; arg1] ~init:defs ~f:(List.Assoc.remove ~equal) in
      (if List.Assoc.mem defs dest ~equal
      then List.Assoc.find_exn defs dest ~equal :: dels else dels),
      List.Assoc.add defs dest i ~equal
    | Unary ((dest, _), _, arg) ->
      let defs = List.Assoc.remove defs arg ~equal in
      (if List.Assoc.mem defs dest ~equal
      then List.Assoc.find_exn defs dest ~equal :: dels else dels),
      List.Assoc.add defs dest i ~equal
    | Jmp _ -> dels, defs
    | Br (arg, _, _) -> dels, List.Assoc.remove defs arg ~equal
    | Call (Some (dest, _), _, args) ->
      let defs = List.fold args ~init:defs ~f:(List.Assoc.remove ~equal) in
      (if List.Assoc.mem defs dest ~equal
      then List.Assoc.find_exn defs dest ~equal :: dels else dels),
      List.Assoc.add defs dest i ~equal
    | Call (None, _, args) ->
      dels, List.fold args ~init:defs ~f:(List.Assoc.remove ~equal)
    | Ret (Some arg) -> dels, List.Assoc.remove defs arg ~equal
    | Ret None -> dels, defs
    | Print args -> dels, List.fold args ~init:defs ~f:(List.Assoc.remove ~equal)
    | Nop -> dels, defs
    | Phi ((dest, _), args, _, _) ->
      let defs = List.fold args ~init:defs ~f:(List.Assoc.remove ~equal) in
      (if List.Assoc.mem defs dest ~equal
      then List.Assoc.find_exn defs dest ~equal :: dels else dels),
      List.Assoc.add defs dest i ~equal in
  let unused = List.foldi ~f ~init:([], []) instrs |> fst in
  let instrs' = List.filteri instrs
    ~f:(fun i _ -> List.mem unused i ~equal:Int.equal |> not) in
  if Int.equal (List.length instrs') (List.length instrs)
  then instrs' else elim_dead_block instrs'

let elim_dead_local (func : Bril.func) : Bril.func =
  let Bril.{ blocks; _ } = Bril.to_blocks_and_cfg func.instrs in
  { func with instrs = List.map blocks ~f:snd
    |> List.map ~f:elim_dead_block
    |> List.fold ~init:[] ~f:(@) }

let rec elim_dead_global (func : Bril.func) : Bril.func =
  let equal = String.equal in
  let f (i : int) (defs, uses : (string * int) list * string list) (instr : Bril.instr) =
    match instr with
    | Label _ -> defs, uses
    | Const ((dest, _), _) ->
      (if not (List.mem uses dest ~equal)
      then List.Assoc.add defs dest i ~equal
      else defs), uses
    | Binary ((dest, _), _, arg0, arg1) ->
      let uses = arg0 :: arg1 :: uses in
      (if not (List.mem uses dest ~equal)
      then List.Assoc.add defs dest i ~equal
      else defs), uses
    | Unary ((dest, _), _, arg) ->
      let uses = arg :: uses in
      (if not (List.mem uses dest ~equal)
      then List.Assoc.add defs dest i ~equal
      else defs), uses
    | Jmp _ -> defs, uses
    | Br (arg, _, _) -> defs, arg :: uses
    | Call (Some (dest, _), _, args) ->
      let uses = args @ uses in
      (if not (List.mem uses dest ~equal)
      then List.Assoc.add defs dest i ~equal
      else defs), uses
    | Call (None, _, args) -> defs, args @ uses
    | Ret (Some arg) -> defs, arg :: uses
    | Ret None -> defs, uses
    | Print args -> defs, args @ uses
    | Nop -> defs, uses
    | Phi ((dest, _), args, _, _) ->
      let uses = args @ uses in
      (if not (List.mem uses dest ~equal)
      then List.Assoc.add defs dest i ~equal
      else defs), uses in
  let defs, uses = List.foldi ~f ~init:([], []) func.instrs in
  let unused = 
    List.filter defs ~f:(fun (v, _) -> List.mem uses v ~equal |> not)
    |> List.map ~f:snd in
  let instrs' = List.filteri func.instrs 
    ~f:(fun i _ -> not (List.mem unused i ~equal:Int.equal)) in
  if Int.equal (List.length func.instrs) (List.length instrs')
  then { func with instrs = instrs' }
  else elim_dead_global { func with instrs = instrs' }

let elim_unreachable (func : Bril.func) : Bril.func =
  let instrs = func.instrs in
  let cfg = Bril.to_blocks_and_cfg instrs in
  let entry = List.hd_exn cfg.blocks |> fst in
  let f (b, _) =
    let preds = get_preds b cfg in
    not (List.is_empty preds) || (equal entry b) in
  { func with instrs =
      cfg.blocks
      |> List.filter ~f
      |> List.map ~f:snd
      |> List.fold ~init:[] ~f:(@) }

let elim_trivial_jumps (func : Bril.func) : Bril.func =
  let g l = function
    | Bril.Label l' -> not (equal l l')
    | _ -> true in
  let f i instr =
    match instr with
    | Bril.Jmp l ->
      List.nth func.instrs (i+1)
      |> Option.value_map ~default:true ~f:(g l)
    | _ -> true in
  { func with instrs = List.filteri func.instrs ~f }

let elim_dead (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:elim_dead_global
    |> List.map ~f:elim_dead_local
    |> List.map ~f:elim_unreachable
    |> List.map ~f:elim_trivial_jumps
  }