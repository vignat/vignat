open Core
open Ir
open Parser_util


let () =
  let ir = ir_of_sexp (Sexp.of_string (In_channel.read_all Sys.argv.(1))) in
  let executions = parse_file Sys.argv.(2) in
  ignore (Analysis.induce_symbolic_assignments ir executions)
