open Core

type bril_type =
  | IntType
  | BoolType
  | FloatType
[@@deriving sexp_of]

type const =
  | Int of int
  | Bool of bool
  | Float of float
[@@deriving sexp_of]

type dest = string * bril_type [@@deriving sexp_of]

type label = string [@@deriving sexp_of]

type arg = string [@@deriving sexp_of]

type func_name = string [@@deriving sexp_of]

type binop =
  | Add
  | Mul
  | Sub
  | Div
  | Eq
  | Lt
  | Gt
  | Le
  | Ge
  | And
  | Or
  | Fadd
  | Fmul
  | Fsub
  | Fdiv
  | Feq
  | Flt
  | Fgt
  | Fle
  | Fge
[@@deriving sexp_of]

type unop =
  | Not
  | Id
[@@deriving sexp_of]

type instr =
  | Label of label
  | Const of dest * const
  | Binary of dest * binop * arg * arg
  | Unary of dest * unop * arg
  | Jmp of label
  | Br of arg * label * label
  | Call of dest option * func_name * arg list
  | Ret of arg option
  | Print of arg list
  | Nop
[@@deriving sexp_of]

type func = {
  name : func_name;
  args : dest list;
  ret_type : bril_type option;
  instrs : instr list;
}
[@@deriving sexp_of]

type t = { funcs : func list } [@@deriving sexp_of]

type cfg = {
  blocks : instr list String.Map.t;
  edges : string list String.Map.t;
} [@@deriving sexp_of]

val to_blocks_and_cfg : instr list -> cfg

val from_file : string -> t

val from_string : string -> t

val to_string : t -> string