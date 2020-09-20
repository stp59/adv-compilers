open Core

let elim_dead_block (instrs : Bril.instr list) : Bril.instr list =
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
    | Nop -> dels, defs in
  let unused = List.foldi ~f ~init:([], []) instrs |> fst in
  (* let unused = dels @ (List.map defs ~f:snd) in *)
  let instrs' = List.filteri instrs
    ~f:(fun i _ -> List.mem unused i ~equal:Int.equal |> not) in
  instrs'

let elim_dead_local (func : Bril.func) : Bril.func =
  let Bril.{ blocks; _ } = Bril.to_blocks_and_cfg func.instrs in
  { func with instrs = List.map blocks ~f:snd
    |> List.map ~f:elim_dead_block
    |> List.fold ~init:[] ~f:(fun acc is -> is @ acc) }

let rec elim_dead_global (func : Bril.func) : Bril.func =
  let f (i : int) (acc : (string * int) list) (instr : Bril.instr) =
    match instr with
    | Label _ -> acc
    | Const ((dest, _), _) ->
      (dest, i) :: (List.filter acc ~f:(fun (a, _) -> not (String.equal a dest)))
    | Binary ((dest, _), _, arg0, arg1) ->
      (dest, i) :: List.filter acc
        ~f:(fun (a, _) -> not (List.mem [dest; arg0; arg1] a ~equal:String.equal))
    | Unary ((dest, _), _, arg) ->
      (dest, i) :: List.filter acc
        ~f:(fun (a, _) -> not (List.mem [dest; arg] a ~equal:String.equal))
    | Jmp _ -> acc
    | Br (arg, _, _) ->
      List.filter acc ~f:(fun (a, _) -> not (String.equal a arg))
    | Call (Some (dest, _), _, args) ->
      (dest, i) :: List.filter acc
        ~f:(fun (a, _) -> not (List.mem args a ~equal:String.equal))
    | Call (None, _, args) ->
      List.filter acc ~f:(fun (a, _) -> not (List.mem args a ~equal:String.equal))
    | Ret (Some arg) ->
      List.filter acc ~f:(fun (a, _) -> not (String.equal a arg))
    | Ret None -> acc
    | Print args ->
      List.filter acc ~f:(fun (a, _) -> not (List.mem args a ~equal:String.equal))
    | Nop -> acc in
  let unused = List.foldi ~f ~init:[] func.instrs |> List.map ~f:snd in
  let instrs' = List.filteri func.instrs 
    ~f:(fun i _ -> not (List.mem unused i ~equal:Int.equal)) in
  if Int.equal (List.length func.instrs) (List.length instrs')
  then { func with instrs = instrs' }
  else elim_dead_global { func with instrs = instrs' }

let elim_dead (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:elim_dead_global
    |> List.map ~f:elim_dead_local
  }