type expr = Core_kernel.Core_sexp.t
val __expr_of_sexp__ : expr -> expr
val expr_of_sexp : expr -> expr
val sexp_of_expr : expr -> expr
type field = { fname : bytes; value : struct_val; addr : int64; }
and struct_val = { full : expr option; break_down : field list; }
val __field_of_sexp__ : expr -> field
val field_of_sexp : expr -> field
val __struct_val_of_sexp__ : expr -> struct_val
val struct_val_of_sexp : expr -> struct_val
val sexp_of_field : field -> expr
val sexp_of_struct_val : struct_val -> expr
type ptee = { before : struct_val; after : struct_val; }
val __ptee_of_sexp__ : expr -> ptee
val ptee_of_sexp : expr -> ptee
val sexp_of_ptee : ptee -> expr
type pointer = Nonptr | Funptr of bytes | Apathptr | Curioptr of ptee
val __pointer_of_sexp__ : expr -> pointer
val pointer_of_sexp : expr -> pointer
val sexp_of_pointer : pointer -> expr
type arg = { aname : bytes; value : expr; ptr : pointer; }
val __arg_of_sexp__ : expr -> arg
val arg_of_sexp : expr -> arg
val sexp_of_arg : arg -> expr
type extra_ptr = { pname : bytes; value : int64; ptee : ptee; }
val __extra_ptr_of_sexp__ : expr -> extra_ptr
val extra_ptr_of_sexp : expr -> extra_ptr
val sexp_of_extra_ptr : extra_ptr -> expr
type ret = { value : expr; ptr : pointer; }
val __ret_of_sexp__ : expr -> ret
val ret_of_sexp : expr -> ret
val sexp_of_ret : ret -> expr
type call_node = {
  fun_name : bytes;
  args : arg list;
  ret : ret option;
  extra_ptrs : extra_ptr list;
  call_context : expr list;
  ret_context : expr list;
  id : int;
}
val __call_node_of_sexp__ : expr -> call_node
val call_node_of_sexp : expr -> call_node
val sexp_of_call_node : call_node -> expr
type trace_prefix = { history : call_node list; tip_calls : call_node list; }
val __trace_prefix_of_sexp__ : expr -> trace_prefix
val trace_prefix_of_sexp : expr -> trace_prefix
val sexp_of_trace_prefix : trace_prefix -> expr
