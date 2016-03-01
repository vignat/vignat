open Core.Std
open Sexp
open Trace_prefix

type tp = Trace_prefix.trace_prefix

let () =
  let y = Sexp.load_sexp "tst.klee" in
  let tp = Trace_prefix.trace_prefix_of_sexp y in
  Sexp.pp Format.std_formatter (Trace_prefix.sexp_of_trace_prefix tp)
