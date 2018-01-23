open Core
open Assumption_lexer
open Parser_util

let parse_n_print filename =
  let rez = parse_file filename in
  List.iter rez ~f:(fun asses ->
      List.iter asses ~f:(fun ass ->
          printf "%s\n" (Ir.render_tterm ass)))

let () =
  parse_n_print Sys.argv.(1)
