open Opt
open Core

let json = In_channel.input_all In_channel.stdin

let ast = Bril.parse json

let sum = Contrived.sum_consts ast

let () = printf "The sum of all the constants is: %d\n" sum