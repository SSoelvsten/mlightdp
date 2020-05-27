open Exception
open Printf

(* --------------------------------------------------------------------------
 * I/O
 * -------------------------------------------------------------------------- *)
let remove_extension filename =
  List.fold_left (fun acc s ->
      if acc = "" then s
      else match s with
        | "mldp" -> acc
        | _ -> acc^"."^s)
    ""
    (String.split_on_char '.' filename)

let add_missing_extension given_filename bare_filename =
  if given_filename = bare_filename then bare_filename^".mldp" else given_filename

let string_from_file filename : string option =
  let lines = ref ""
  in let channel = open_in filename
  in try
      while true
      do
        lines := (!lines)^(input_line channel)^"\n"
      done;
      Some(!lines)
    with
     | End_of_file -> (close_in channel; Some(!lines))
     | e -> raise e

let string_to_file (filename: string) (output: string) : unit =
  let channel = open_out filename
  in output_string channel output;
     close_out channel

let dafny_preamble = "src/dafny_preamble.dfy"


(* --------------------------------------------------------------------------
 * MAIN
 * -------------------------------------------------------------------------- *)
let () =
  if Array.length Sys.argv < 1
  then print_string "File name missing"
  else let given_file = Sys.argv.(1)
    in let bare_file = remove_extension given_file
    in let output_file = bare_file^".dfy"
    in let input_stream = open_in (add_missing_extension given_file bare_file)
    in let lexbuf = Lexing.from_channel input_stream
    in let typed_ast = lexbuf
                       (* Parsing *)
                       |> Parser.main_prog Lexer.tokenize
                       (* Semantic Analysis *)
                       |> Semant.s_prog
    in let dp_ast = typed_ast
                     (* Refinement Step *)
                     |> Refine.r_prog
                     (* Differential Privacy *)
                     |> Dp.t_prog
       in let preamble = string_from_file dafny_preamble
       in match preamble with
          | None -> ()
          | Some(pream) -> (pream^(Prdafny.pty_prog dp_ast Prdafny.init_ctxt))
                           |> string_to_file output_file
