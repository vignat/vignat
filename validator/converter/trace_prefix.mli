type expr = bytes
val __expr_of_sexp__ : Core_kernel.Core_sexp.t -> expr
val expr_of_sexp : Core_kernel.Core_sexp.t -> expr
val sexp_of_expr : expr -> Core_kernel.Core_sexp.t
type field = { name : expr; value : struct_val; }
and struct_val = { full : expr; break_down : field list; }
val __field_of_sexp__ : Core_kernel.Core_sexp.t -> field
val field_of_sexp : Core_kernel.Core_sexp.t -> field
val __struct_val_of_sexp__ : Core_kernel.Core_sexp.t -> struct_val
val struct_val_of_sexp : Core_kernel.Core_sexp.t -> struct_val
val sexp_of_field : field -> Core_kernel.Core_sexp.t
val sexp_of_struct_val : struct_val -> Core_kernel.Core_sexp.t
type ptee = {
  is_fun_ptr : bool;
  fun_name : expr option;
  before : struct_val option;
  after : struct_val option;
}
val __ptee_of_sexp__ : Core_kernel.Core_sexp.t -> ptee
val ptee_of_sexp : Core_kernel.Core_sexp.t -> ptee
val sexp_of_ptee : ptee -> Core_kernel.Core_sexp.t
type arg = {
  name : expr;
  value : struct_val;
  is_ptr : bool;
  pointee : ptee option;
}
val __arg_of_sexp__ : Core_kernel.Core_sexp.t -> arg
val arg_of_sexp : Core_kernel.Core_sexp.t -> arg
val sexp_of_arg : arg -> Core_kernel.Core_sexp.t
type ret = { value : struct_val; is_ptr : bool; pointee : ptee option; }
val __ret_of_sexp__ : Core_kernel.Core_sexp.t -> ret
val ret_of_sexp : Core_kernel.Core_sexp.t -> ret
val sexp_of_ret : ret -> Core_kernel.Core_sexp.t
type call_node = {
  fun_name : expr;
  args : arg list;
  ret : ret option;
  call_context : expr list;
  ret_context : expr list;
}
val __call_node_of_sexp__ : Core_kernel.Core_sexp.t -> call_node
val call_node_of_sexp : Core_kernel.Core_sexp.t -> call_node
val sexp_of_call_node : call_node -> Core_kernel.Core_sexp.t
type trace_prefix = { history : call_node list; tip_calls : call_node list; }
val __trace_prefix_of_sexp__ : Core_kernel.Core_sexp.t -> trace_prefix
val trace_prefix_of_sexp : Core_kernel.Core_sexp.t -> trace_prefix
val sexp_of_trace_prefix : trace_prefix -> Core_kernel.Core_sexp.t
