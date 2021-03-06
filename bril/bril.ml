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
[@@deriving sexp_of, equal]

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
[@@deriving sexp_of, equal]

let binops_by_name =
  [
    ("add", Add);
    ("mul", Mul);
    ("sub", Sub);
    ("div", Div);
    ("eq", Eq);
    ("lt", Lt);
    ("gt", Gt);
    ("le", Le);
    ("ge", Ge);
    ("and", And);
    ("or", Or);
    ("fadd", Fadd);
    ("fmul", Fmul);
    ("fsub", Fsub);
    ("fdiv", Fdiv);
    ("feq", Feq);
    ("flt", Flt);
    ("fgt", Fgt);
    ("fle", Fle);
    ("fge", Fge);
  ]

let binops_by_op = List.map binops_by_name ~f:(fun (a, b) -> (b, a))

type unop =
  | Not
  | Id
[@@deriving sexp_of, equal]

let unops_by_name = [ ("not", Not); ("id", Id) ]

let unops_by_op = List.map unops_by_name ~f:(fun (a, b) -> (b, a))

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
  | Phi of dest * arg list * label list * dest
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
  blocks : (string * instr list) list;
  edges : (string * string list) list;
  order : string list;
} [@@deriving sexp_of]

let update_edges blocks =
  List.mapi blocks ~f:(fun i (name, block) ->
    let next = match List.last_exn block with
      | Jmp label -> [ label ]
      | Br (_, l1, l2) -> [ l1; l2 ]
      | Ret _ -> []
      | _ -> begin match List.nth blocks (i + 1) with
        | None -> []
        | Some (label, _) -> [ label ] end in
    (name, next))

let to_blocks_and_cfg instrs =
  let block_name i = sprintf "b%d" (i + 1) in
  let (name, block, blocks) =
    List.fold instrs
      ~init:(block_name 0, [], [])
      ~f:(fun (name, block, blocks) instr ->
        match instr with
        | Label n -> (n, [instr], (name, List.rev block) :: blocks)
        | Jmp _
        | Br _
        | Ret _ ->
            let blocks = (name, List.rev (instr :: block)) :: blocks in
            (block_name (List.length blocks), [], blocks)
        | _ -> (name, instr :: block, blocks))
  in
  let blocks =
    (name, List.rev block) :: blocks
    |> List.filter ~f:(fun (_, block) -> not (List.is_empty block))
  in
  let blocks = List.rev blocks in
  let edges = update_edges blocks in
  let order = List.map blocks ~f:fst in
  { blocks; edges; order; }

let from_json json =
  let open Yojson.Basic.Util in
  let has_key json key =
    match json |> member key with
    | `Null -> false
    | _ -> true
  in
  let to_list = function
    | `Null -> []
    | json -> to_list json
  in
  let to_type = function
    | `String "int" -> IntType
    | `String "bool" -> BoolType
    | `String "float" -> FloatType
    | `Assoc [ ("ptr", _)] -> failwith "invalid type: ptr"
    | json -> failwithf "invalid type: %s" (json |> to_string) ()
  in
  let to_type_option = function
    | `Null -> None
    | json -> Some (to_type json)
  in
  let to_arg json = (json |> member "name" |> to_string, json |> member "type" |> to_type) in

  let to_instr json =
    match json |> member "label" with
    | `String label -> Label label
    | `Null -> (
        let dest () = (json |> member "dest" |> to_string, json |> member "type" |> to_type) in
        let args () = json |> member "args" |> to_list |> List.map ~f:to_string in
        let labels () = json |> member "labels" |> to_list |> List.map ~f:to_string in
        let arg = List.nth_exn (args ()) in
        let label = List.nth_exn (labels ()) in
        let mem = List.Assoc.mem ~equal:String.equal in
        let find = List.Assoc.find_exn ~equal:String.equal in
        match json |> member "op" |> to_string with
        | "const" ->
            let const =
              match json |> member "type" |> to_type with
              | IntType -> Int (json |> member "value" |> to_int)
              | BoolType -> Bool (json |> member "value" |> to_bool)
              | FloatType -> Float (json |> member "value" |> (function
                | `Float _ as f -> to_float f
                | `Int _ as f -> to_int f |> float_of_int
                | _ -> failwith "invalid const"))
            in
            Const (dest (), const)
        | op when mem binops_by_name op -> Binary (dest (), find binops_by_name op, arg 0, arg 1)
        | op when mem unops_by_name op -> Unary (dest (), find unops_by_name op, arg 0)
        | "jmp" -> Jmp (label 0)
        | "br" -> Br (arg 0, label 0, label 1)
        | "call" ->
            Call
              ( (if has_key json "dest" then Some (dest ()) else None),
                json |> member "funcs" |> to_list |> List.hd_exn |> to_string,
                args () )
        | "ret" -> Ret (if List.is_empty (args ()) then None else Some (arg 0))
        | "print" -> Print (args ())
        | "nop" -> Nop
        | "phi" -> Phi (dest (), args (), labels (), dest ())
        | op -> failwithf "invalid op: %s" op ())
    | json -> failwithf "invalid label: %s" (json |> to_string) ()
  in
  let to_func json =
    let name = json |> member "name" |> to_string in
    let args = json |> member "args" |> to_list |> List.map ~f:to_arg in
    let ret_type = json |> member "type" |> to_type_option in
    let instrs = json |> member "instrs" |> to_list |> List.map ~f:to_instr in
    { name; args; ret_type; instrs; }
  in
  { funcs = json |> member "functions" |> to_list |> List.map ~f:to_func }

let from_file filename = from_json (Yojson.Basic.from_file filename)

let from_string string = from_json (Yojson.Basic.from_string string)

let to_string { funcs } =
  let of_type = function
    | IntType -> `String "int"
    | BoolType -> `String "bool"
    | FloatType -> `String "float"
  in
  let of_dest (name, bril_type) = [ ("dest", `String name); ("type", of_type bril_type) ] in
  let of_instr = function
    | Label label -> `Assoc [ ("label", `String label) ]
    | Const (dest, const) ->
        `Assoc
          ([
             ("op", `String "const");
             ( "value",
               match const with
               | Int i -> `Int i
               | Bool b -> `Bool b
               | Float f -> `Float f );
           ]
          @ of_dest dest)
    | Binary (dest, op, arg1, arg2) ->
        `Assoc
          ([
             ("op", `String (List.Assoc.find_exn binops_by_op op ~equal:equal_binop));
             ("args", `List [ `String arg1; `String arg2 ]);
           ]
          @ of_dest dest)
    | Unary (dest, op, arg) ->
        `Assoc
          ([
             ("op", `String (List.Assoc.find_exn unops_by_op op ~equal:equal_unop));
             ("args", `List [ `String arg ]);
           ]
          @ of_dest dest)
    | Jmp label -> `Assoc [ ("op", `String "jmp"); ("labels", `List [ `String label ]) ]
    | Br (arg, l1, l2) ->
        `Assoc
          [
            ("op", `String "br");
            ("args", `List [ `String arg ]);
            ("labels", `List [ `String l1; `String l2 ]);
          ]
    | Call (dest, func_name, args) ->
        `Assoc
          ([
             ("op", `String "call");
             ("funcs", `List [ `String func_name ]);
             ("args", `List (List.map args ~f:(fun arg -> `String arg)));
           ]
          @ Option.value_map dest ~default:[] ~f:of_dest)
    | Ret arg ->
        `Assoc
          [
            ("op", `String "ret");
            ("args", Option.value_map arg ~default:`Null ~f:(fun arg -> `List [ `String arg ]));
          ]
    | Print args ->
        `Assoc
          [ ("op", `String "print"); ("args", `List (List.map args ~f:(fun arg -> `String arg))) ]
    | Nop -> `Assoc [ ("op", `String "nop") ]
    (* | _ -> failwith "" *)
    | Phi (dest, args, ls, _) -> 
      `Assoc (
      [ ("op", `String "phi");
        ("args", `List (List.map args ~f:(fun arg -> `String arg)));
        ("labels", `List (List.map ls ~f:(fun l -> `String l))); ] 
        @ of_dest dest)
  in
  let of_func { name; args; ret_type; instrs; _ } =
    if Option.is_some ret_type then
      `Assoc
        [
          ("name", `String name);
          ( "args",
            `List
              (List.map args ~f:(fun (name, bril_type) ->
                  `Assoc [ ("name", `String name); ("type", of_type bril_type) ])) );
          ("type", Option.value_map ret_type ~default:`Null ~f:of_type);
          ("instrs", `List (List.map instrs ~f:of_instr));
        ]
    else 
      `Assoc
        [
          ("name", `String name);
          ( "args",
            `List
              (List.map args ~f:(fun (name, bril_type) ->
                  `Assoc [ ("name", `String name); ("type", of_type bril_type) ])) );
          ("instrs", `List (List.map instrs ~f:of_instr));
        ]
  in
  `Assoc [ ("functions", `List (List.map funcs ~f:of_func)) ] |> Yojson.pretty_to_string