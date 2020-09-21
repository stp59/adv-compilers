open Core

let fresh_num =
  let counter = ref 0 in
  fun () -> let x = !counter in counter := x + 1; x

type local_val =
  | Arg of int
  | Const of Bril.const
  | Binary of Bril.binop * int * int
  | Unary of Bril.unop * int
  | Call of string * int list

type entry = local_val * Bril.dest

type table = entry list

let vals_equal v1 v2 =
  match v1, v2 with
  | Arg n1, Arg n2 -> Int.equal n1 n2
  | Const c1, Const c2 -> Bril.equal_const c1 c2
  | Binary (op1, arg1a, arg2a), Binary (op2, arg1b, arg2b) ->
    Bril.equal_binop op1 op2 && Int.equal arg1a arg1b && Int.equal arg2a arg2b
  | Unary (op1, arg1), Unary (op2, arg2) ->
    Bril.equal_unop op1 op2 && Int.equal arg1 arg2
  | Call (name1, l1), Call (name2, l2) ->
    (String.equal name1 name2) && (List.equal (Int.equal) l1 l2)
  | _, _ -> false

let entry_of_instr (tbl : entry list) (var_num : (string * int) list)
    (instr : Bril.instr) : entry * entry list =
  let equal = String.equal in
  match instr with
  | Const (dest, const) -> (Const const, dest), tbl
  | Binary (dest, op, a0, a1) ->
    let i0 = List.Assoc.find var_num a0 ~equal in
    let i1 = List.Assoc.find var_num a1 ~equal in
    let i0, tbl = match i0 with
      | Some v -> v, tbl
      | None -> List.length tbl, tbl @ [Arg (List.length tbl), (a0, IntType)] in
    let i1, tbl = match i1 with
      | Some v -> v, tbl
      | None -> List.length tbl, tbl @ [Arg (List.length tbl), (a1, IntType)] in
    (Binary (op, i0, i1), dest), tbl
  | Unary (dest, op, a) ->
    let i = List.Assoc.find var_num a ~equal in
    let i, tbl = match i with
      | Some v -> v, tbl
      | None -> List.length tbl, tbl @ [Arg (List.length tbl), (a, IntType)] in
    (Unary (op, i), dest), tbl
  | Call (Some dest, name, args) ->
    let is = List.map args ~f:(List.Assoc.find var_num ~equal) in
    let tbl, is = List.fold_mapi is ~init:tbl
      ~f:(fun j tbl i -> match i with Some v -> tbl, v
        | None -> tbl @ [Arg (List.length tbl), (List.nth_exn args j, IntType)], List.length tbl) in
    (Call (name, is), dest), tbl
  | _ -> failwith "Instruction not a value"

let updates (l : Bril.instr list) (dest : Bril.dest) : bool =
  let dest = fst dest in
  let f instr =
    match instr with
    | Bril.Const ((dest', _), _)
    | Bril.Binary ((dest', _), _, _, _)
    | Bril.Unary ((dest', _), _, _)
    | Bril.Call (Some (dest', _), _, _) -> String.equal dest dest'
    | _ -> false in
  List.exists l ~f

let num_val_block (args : Bril.dest list) (block : Bril.instr list) : Bril.instr list =
  let f i (tbl, var_num, acc) instr =
    match instr with
    | Bril.Label l -> tbl, var_num, Bril.Label l :: acc
    | Bril.Const (dest, c) ->
      let (value, var), tbl = entry_of_instr tbl var_num instr in
      if List.Assoc.mem tbl value ~equal:vals_equal
      then
        let (n, d) = List.findi tbl ~f:(fun i e -> vals_equal (fst e) value)
          |> Option.value ~default:(0, (Const (Int 0), ("", Bril.IntType))) in
        tbl, List.Assoc.add var_num (dest |> fst) n ~equal:String.equal, instr :: acc
      else
        let num = List.length tbl in
        let dest' = if updates (List.drop block (i+1)) dest
          then (sprintf "lvn.%d" num, snd dest) else dest in
        let tbl = tbl @ [ (Const c, dest') ] in
        let instr = Bril.Const (dest', c) in
        tbl, List.Assoc.add
          (List.Assoc.add var_num (dest |> fst) num ~equal:String.equal)
          (dest' |> fst) num ~equal:String.equal, instr :: acc
    | Bril.Binary (dest, op, arg0, arg1) ->
      let (value, var), tbl = entry_of_instr tbl var_num instr in
      if List.Assoc.mem tbl value ~equal:vals_equal
      then
        let (n, d) = List.findi tbl ~f:(fun i e -> vals_equal (fst e) value)
          |> Option.value ~default:(0, (Const (Int 0), ("", Bril.IntType))) in
        tbl, List.Assoc.add var_num (dest |> fst) n ~equal:String.equal, acc
      else
        let i0 = List.Assoc.find var_num arg0 ~equal:String.equal in
        let i1 = List.Assoc.find var_num arg1 ~equal:String.equal in
        let i0, tbl = match i0 with
          | Some v -> v, tbl
          | None -> List.length tbl, tbl @ [Arg (List.length tbl), (arg0, IntType)] in
        let i1, tbl = match i1 with
          | Some v -> v, tbl
          | None -> List.length tbl, tbl @ [Arg (List.length tbl), (arg1, IntType)] in
        let num = List.length tbl in
        let dest' = if updates (List.drop block (i+1)) dest
          then (sprintf "lvn.%d" num, snd dest) else dest in
        let tbl = tbl @ [ (Binary (op, i0, i1), dest') ] in
        let instr = Bril.Binary (dest', op, (List.nth_exn tbl i0 |> snd |> fst),
          List.nth_exn tbl i1 |> snd |> fst) in
        tbl, List.Assoc.add
          (List.Assoc.add var_num (dest |> fst) num ~equal:String.equal)
          (dest' |> fst) num ~equal:String.equal, instr :: acc
    | Bril.Unary (dest, op, arg) ->
      let (value, var), tbl = entry_of_instr tbl var_num instr in
      if List.Assoc.mem tbl value ~equal:vals_equal
      then
        let (n, d) = List.findi tbl ~f:(fun i e -> vals_equal (fst e) value)
          |> Option.value ~default:(0, (Const (Int 0), ("", Bril.IntType))) in
        tbl, List.Assoc.add var_num (dest |> fst) n ~equal:String.equal, acc
      else
        let i0 = List.Assoc.find var_num arg ~equal:String.equal in
        let i0, tbl = match i0 with
          | Some v -> v, tbl
          | None -> List.length tbl, tbl @ [Arg (List.length tbl), (arg, IntType)] in
        let num = List.length tbl in
        let dest' = if updates (List.drop block (i+1)) dest
          then (sprintf "lvn.%d" num, snd dest) else dest in
        let tbl = tbl @ [ (Unary (op, i0), dest') ] in
        let instr = Bril.Unary (dest', op, (List.nth_exn tbl i0 |> snd |> fst)) in
        tbl, List.Assoc.add
          (List.Assoc.add var_num (dest |> fst) num ~equal:String.equal)
          (dest' |> fst) num ~equal:String.equal, instr :: acc
    | Jmp l -> tbl, var_num, Jmp l :: acc
    | Br (arg, l1, l2) ->
      let i = List.Assoc.find var_num arg ~equal:String.equal in
      begin match i with
      | Some v -> tbl, var_num, Br (List.nth_exn tbl v |> snd |> fst, l1, l2) :: acc
      | None -> tbl, var_num, Br (arg, l1, l2) :: acc end
    | Bril.Call (Some dest, name, args) ->
      let (value, var), tbl = entry_of_instr tbl var_num instr in
      if List.Assoc.mem tbl value ~equal:vals_equal
      then
        let (n, d) = List.findi tbl ~f:(fun i e -> vals_equal (fst e) value)
          |> Option.value ~default:(0, (Const (Int 0), ("", Bril.IntType))) in
        tbl, List.Assoc.add var_num (dest |> fst) n ~equal:String.equal, acc
      else
        let is = List.map args
          ~f:(fun arg -> List.Assoc.find var_num arg ~equal:String.equal) in
        let tbl, is = List.fold_mapi is ~init:tbl
          ~f:(fun j tbl i -> match i with Some v -> tbl, v
            | None -> tbl @ [Arg (List.length tbl), (List.nth_exn args j, IntType)], List.length tbl) in
        let num = List.length tbl in
        let dest' = if updates (List.drop block (i+1)) dest
          then (sprintf "lvn.%d" num, snd dest) else dest in
        let tbl = tbl @ [ (Call (name, is), dest') ] in
        let instr = Bril.Call (Some dest', name,
          List.map is ~f:(fun i -> List.nth_exn tbl i |> snd |> fst)) in
        tbl, List.Assoc.add
          (List.Assoc.add var_num (dest |> fst) num ~equal:String.equal)
          (dest' |> fst) num ~equal:String.equal, instr :: acc
    | Call (None, name, args) ->
      let args' = List.mapi args
        ~f:(fun i arg -> List.Assoc.find var_num arg ~equal:String.equal
          |> Option.map ~f:(fun v -> List.nth_exn tbl v |> snd |> fst)
          |> Option.value ~default:(List.nth_exn args i)) in
      tbl, var_num, Call (None, name, args') :: acc
    | Ret (Some arg) ->
      tbl, var_num, Ret (Some (List.Assoc.find var_num arg ~equal:String.equal
        |> Option.map ~f:(fun v -> List.nth_exn tbl v |> snd |> fst)
        |> Option.value ~default:arg)) :: acc
    | Ret None -> tbl, var_num, Ret None :: acc
    | Print args ->
      let args' = List.mapi args
        ~f:(fun i arg -> List.Assoc.find var_num arg ~equal:String.equal
          |> Option.map ~f:(fun v -> List.nth_exn tbl v |> snd |> fst)
          |> Option.value ~default:(List.nth_exn args i)) in
      tbl, var_num, Print args' :: acc
    | Nop -> tbl, var_num, Nop :: acc in
  let tbl_init = List.mapi args ~f:(fun i dest -> (Arg i ,dest)) in
  let var_num_init = List.mapi args ~f:(fun i dest -> (fst dest, i)) in
  List.foldi block ~init:(tbl_init, var_num_init, []) ~f |> Tuple.T3.get3 |> List.rev

let num_val_func (func : Bril.func) : Bril.func =
  let Bril.{ blocks; _ } = Bril.to_blocks_and_cfg func.instrs in
  { func with instrs = List.map blocks ~f:snd
    |> List.map ~f:(num_val_block func.args)
    |> List.fold ~init:[] ~f:(fun acc is -> is @ acc) }

let num_val (bril : Bril.t) : Bril.t =
  { funcs = List.map ~f:num_val_func bril.funcs }