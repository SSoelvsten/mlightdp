open Ast

exception NotImplemented of string
exception DevMessage of string
exception CompilationFail

let print_error lnum (msg: string) =
  let lnum' = match lnum with
    | Some(i) -> string_of_int i
    | None    -> "_"
  in
  "Error("^lnum'^"): "^msg^"\n" |> print_string

let print_warning lnum (msg: string) =
  let lnum' = match lnum with
    | Some(i) -> string_of_int i
    | None    -> "_"
  in
  "Warning("^lnum'^"): "^msg^"\n" |> print_string