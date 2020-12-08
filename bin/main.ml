open Opt
open Core
open Command.Spec

let contrived_doc = "sum the value of all constants (ints and bools) and emit on stdout"
let nop_doc = "parse the bril json into the OCaml datastructure, then deparse back into json and emit on stdout"
let tdce_doc = "perform trivial dead code elimination"
let lvn_doc = "perform local value numbering followed by tdce"
let cp_doc = "perform the constant propagation optimization via dataflow analaysis"
let to_ssa_doc = "convert the program to SSA"
let of_ssa_doc = "convert the program from SSA"
let licm_doc = "perform loop-invariant code motion"

let (>>|) opt func = Option.map ~f:func opt

let do_contrived () =
  let json = In_channel.input_all Stdlib.stdin in
  let ast = Bril.from_string json in
  let sum = Contrived.sum_consts ast in
  printf "The sum of all the constants is: %d\n" sum

let do_nop () =
  In_channel.input_all Stdlib.stdin
  |> Bril.from_string
  |> Bril.to_string
  |> Out_channel.output_string Stdlib.stdout

let do_tdce () =
  In_channel.input_all Stdlib.stdin
  |> Bril.from_string
  |> Tdce.elim_dead
  |> Bril.to_string
  |> Out_channel.output_string Stdlib.stdout

let do_lvn () =
  In_channel.input_all In_channel.stdin
  |> Bril.from_string
  |> Lvn.num_val
  |> Tdce.elim_dead
  |> Bril.to_string
  |> Out_channel.output_string Out_channel.stdout

let do_cp () =
  In_channel.input_all In_channel.stdin
  |> Bril.from_string
  |> Dataflow.cp
  |> Tdce.elim_dead
  |> Bril.to_string
  |> Out_channel.output_string Out_channel.stdout

let do_to_ssa () =
  In_channel.input_all In_channel.stdin
  |> Bril.from_string
  |> Ssa.ssa_of_bril
  |> Tdce.elim_dead
  |> Bril.to_string
  |> Out_channel.output_string Out_channel.stdout

let do_of_ssa () =
  In_channel.input_all In_channel.stdin
  |> Bril.from_string
  |> Ssa.bril_of_ssa
  |> Dataflow.cp
  |> Bril.to_string
  |> Out_channel.output_string Out_channel.stdout

let do_licm () =
  In_channel.input_all In_channel.stdin
  |> Bril.from_string
  |> Licm.move_code
  |> Tdce.elim_dead
  |> Bril.to_string
  |> Out_channel.output_string Out_channel.stdout

let do_command (contrived : bool) (nop : bool) (tdce : bool)
    (lvn : bool) (cp : bool) (to_ssa : bool) (of_ssa : bool) (licm : bool) : unit =
  if contrived then do_contrived ()
  else if nop then do_nop ()
  else if tdce then do_tdce ()
  else if lvn then do_lvn ()
  else if cp then do_cp ()
  else if to_ssa then do_to_ssa ()
  else if of_ssa then do_of_ssa ()
  else if licm then do_licm ()
  else print_endline "Usage: bril-opt [flags]"

let spec = 
  empty
  +> flag "--contrived" no_arg ~doc:contrived_doc
  +> flag "--nop" no_arg ~doc:nop_doc
  +> flag "--tdce" no_arg ~doc:tdce_doc
  +> flag "--lvn" no_arg ~doc:lvn_doc
  +> flag "--cp" no_arg ~doc:cp_doc
  +> flag "--tossa" no_arg ~doc:to_ssa_doc
  +> flag "--ofssa" no_arg ~doc:of_ssa_doc
  +> flag "--licm" no_arg ~doc:licm_doc

let command = Command.basic_spec
  ~summary:"A collection of optimizations/transformations on the sample low-level intermediate langauge bril."
  ~readme:(fun () -> "Flags take the json representation of bril programs from standard input and output the transformed bril json on standard output.")
  spec (fun contrived nop tdce lvn cp to_ssa of_ssa licm () ->
    do_command contrived nop tdce lvn cp to_ssa of_ssa licm)

let () = Command.run ~version:"1.0" ~build_info:"something" command