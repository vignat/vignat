open Core.Std
open Sexp
open Trace_prefix

type tp = Trace_prefix.trace_prefix

let () =
  let y = Sexp.load_sexp "tst.klee" in
  let tp = Trace_prefix.trace_prefix_of_sexp y in 
  let lala = tp (*{history=[];
              tip_calls=[{fun_name="aa";
                          args=[{name="c";
                                 value={full="14414"; break_down=[]};
                                 is_ptr=true;
                                 pointee=Some {is_fun_ptr=true;
                                               fun_name = Some "fafa";
                                               before = None;
                                               after = None;}}]; ret=None;
                          call_context=[];
                          ret_context=[]}]}*) in
  printf "ololo%s\n" (Sexp.to_string (Trace_prefix.sexp_of_trace_prefix lala))
