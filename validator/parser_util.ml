open Core
open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Assumption_parser.execution_list Assumption_lexer.read lexbuf with
  | Assumption_lexer.SyntaxError msg ->
    fprintf stderr "%a:%s\n" print_position lexbuf msg;
    []
  | Assumption_parser.Error ->
    fprintf stderr "%a: parser error\n" print_position lexbuf;
    exit(-1)

let parse_file filename =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename};
  parse_with_error lexbuf
