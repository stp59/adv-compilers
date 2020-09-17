open Opt
open Core
open Command.Spec

let help_doc = "TODO: help menu unimplemented"
let contrived_doc = "TODO: contrived docuementation unimplemented"

let (>>|) opt func = Option.map ~f:func opt

let do_help () =
  print_endline help_doc

let do_contrived () =
  (* let ic = Stdlib.open_in filename in *)
  let json = In_channel.input_all Stdlib.stdin in
  let ast = Bril.from_string json in
  let sum = Contrived.sum_consts ast in
  printf "The sum of all the constants is: %d\n" sum

let do_command (help : bool) (contrived : bool) : unit =
  if help then do_help ()
  else if contrived then do_contrived ()
  else do_help ()

let spec = 
  empty
  +> flag "--help" no_arg ~doc:help_doc
  +> flag "--contrived" no_arg ~doc:contrived_doc

let command = Command.basic_spec
  ~summary:"summary is empty for now"
  ~readme:(fun () -> "also empty for now")
  spec (fun help contrived () -> do_command help contrived)

let () = Command.run ~version:"1.0" ~build_info:"something" command