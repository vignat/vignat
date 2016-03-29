
open Core.Std.Sexp
open Sexplib.Conv

type expr = Core.Std.Sexp.t with sexp

type field = {fname: string; value: struct_val}
and struct_val = {full: expr; break_down: field list;} with sexp

type ptee = {is_fun_ptr: bool; fun_name: string option;
             before: struct_val option;
             after: struct_val option;} with sexp

type arg = {aname: string; value: struct_val; is_ptr: bool;
            pointee: ptee option;} with sexp

type ret = {value: struct_val; is_ptr: bool; pointee: ptee option;} with sexp

type call_node = {fun_name: string; args: arg list; ret: ret option;
                  call_context: expr list; ret_context: expr list;} with sexp

type trace_prefix = {history: call_node list; tip_calls: call_node list;} with sexp
