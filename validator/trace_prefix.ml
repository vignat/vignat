
open Core.Std.Sexp
open Sexplib.Conv

type expr = Core.Std.Sexp.t with sexp

type field = {fname: string; value: struct_val; addr: int64}
and struct_val = {full: expr option; break_down: field list;} with sexp

type ptee = {before: struct_val; after: struct_val;} with sexp

type ex_ptee = Opening of struct_val
             | Closing of struct_val
             | Changing of (struct_val*struct_val)
with sexp

type pointer =
  | Nonptr
  | Funptr of string
  | Apathptr
  | Curioptr of ptee
with sexp

type arg = {aname: string; value: expr; ptr: pointer;} with sexp

type extra_ptr = {pname: string; value: int64; ptee: ex_ptee;} with sexp

type ret = {value: expr; ptr: pointer;} with sexp

type call_node = {fun_name: string; args: arg list; ret: ret option;
                  extra_ptrs: extra_ptr list;
                  call_context: expr list; ret_context: expr list;
                  id: int with default(0)} with sexp

type trace_prefix = {history: call_node list; tip_calls: call_node list;} with sexp
