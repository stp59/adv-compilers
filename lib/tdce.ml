open Core

let rec elim_func_dead (func : Bril.func) : Bril.func =
  let f (i : int) (acc : (string * int) list) (instr : Bril.instr) =
    (* print_endline "The following lines define vars that are as of yet unused:";
    List.iter acc ~f:(fun (_, i) -> print_endline (sprintf "\t%d" i)); *)
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
  else elim_func_dead { func with instrs = instrs' }

let elim_dead (bril : Bril.t) : Bril.t =
  { funcs = List.map bril.funcs ~f:elim_func_dead }