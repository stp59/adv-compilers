open Bril

let rec sum_consts (bril : Bril.t) : int =
  List.fold_left add_func_consts 0 bril.funcs

and add_func_consts (acc : int) (func : Bril.func) : int =
  List.fold_left add_instr_consts acc func.instrs

and add_instr_consts (acc : int) (instr : Bril.instr) : int =
  (* print_endline ("acc is: " ^ string_of_int acc); *)
  match instr with
  | Const (_, Int n) -> acc + n
  | Const (_, Bool b) -> acc + (if b then 1 else 0)
  | _ -> acc