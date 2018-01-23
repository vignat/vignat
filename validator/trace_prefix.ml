
open Core.Sexp
open Sexplib.Conv

type expr = Core.Sexp.t [@@deriving sexp]

type field = {fname: string; value: struct_val; addr: int64}
and struct_val = {sname: string option;
                  full: expr option;
                  break_down: field list;} [@@deriving sexp]

type ptee = {before: struct_val; after: struct_val;} [@@deriving sexp]

type ex_ptee = Opening of struct_val
             | Closing of struct_val
             | Changing of (struct_val*struct_val) [@@deriving sexp]

type pointer =
  | Nonptr
  | Funptr of string
  | Apathptr
  | Curioptr of ptee [@@deriving sexp]

type arg = {aname: string; value: expr; ptr: pointer;} [@@deriving sexp]

type extra_ptr = {pname: string; value: int64; ptee: ex_ptee;} [@@deriving sexp]

type ret = {value: expr; ptr: pointer;} [@@deriving sexp]

type call_node = {fun_name: string; args: arg list; ret: ret option;
                  extra_ptrs: extra_ptr list;
                  call_context: expr list; ret_context: expr list;
                  id: int [@default 0];} [@@deriving sexp]

type trace_prefix = {history: call_node list; tip_calls: call_node list;} [@@deriving sexp]
