open Opt
open Core
open Command.Spec

let help_doc = "TODO: help menu unimplemented"
let contrived_doc = "TODO: contrived documentation unimplemented"
let nop_doc = "TODO: nop documentation unimplemented"
let tdce_doc = "TODO: tdce documentation unimplemented"

let (>>|) opt func = Option.map ~f:func opt

let do_help () =
  print_endline help_doc

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
  |> fun x -> x
  |> Bril.to_string
  |> Out_channel.output_string Stdlib.stdout

let do_command (help : bool) (contrived : bool) (nop : bool) (tdce : bool) : unit =
  if help then do_help ()
  else if contrived then do_contrived ()
  else if nop then do_nop ()
  else if tdce then do_tdce ()
  else do_help ()

let spec = 
  empty
  +> flag "--help" no_arg ~doc:help_doc
  +> flag "--contrived" no_arg ~doc:contrived_doc
  +> flag "--nop" no_arg ~doc:nop_doc
  +> flag "--tdce" no_arg ~doc:tdce_doc

let command = Command.basic_spec
  ~summary:"summary is empty for now"
  ~readme:(fun () -> "also empty for now")
  spec (fun help contrived nop tdce () -> do_command help contrived nop tdce)

let () = Command.run ~version:"1.0" ~build_info:"something" command