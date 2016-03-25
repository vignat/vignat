type bop = Eq | Le | Lt | Ge | Gt | Add | Sub | And
type ttype =
    Ptr of ttype
  | Sint32
  | Uint32
  | Uint16
  | Uint8
  | Void
  | Str of bytes * (bytes * ttype) list
  | Ctm of bytes
  | Fptr of bytes
  | Boolean
  | Sunknown
  | Uunknown
  | Unknown
type term =
    Bop of bop * tterm * tterm
  | Apply of bytes * tterm list
  | Id of bytes
  | Struct of bytes * (bytes * tterm) list
  | Int of int
  | Bool of bool
  | Not of tterm
  | Str_idx of tterm * bytes
  | Deref of tterm
  | Addr of tterm
  | Fptr of bytes
  | Cast of ttype * tterm
  | Undef
and tterm = { v : term; t : ttype; }
val ttype_to_str : ttype -> bytes
val is_void : ttype -> bool
val get_pointee : ttype -> ttype
type var_spec = { name : bytes; v : tterm; }
type fun_call_context = {
  pre_lemmas : bytes list;
  application : term;
  post_lemmas : bytes list;
  ret_name : bytes option;
  ret_type : ttype;
}
type call_result = {
  args_post_conditions : var_spec list;
  ret_val : tterm;
  post_statements : tterm list;
}
type hist_call = { context : fun_call_context; result : call_result; }
type tip_call = { context : fun_call_context; results : call_result list; }
type ir = {
  preamble : bytes;
  free_vars : var_spec Core.Std.String.Map.t;
  arguments : var_spec Core.Std.String.Map.t;
  tmps : var_spec Core.Std.String.Map.t;
  cmplxs : var_spec Core.Std.String.Map.t;
  context_assumptions : tterm list;
  calls : hist_call list * tip_call;
  leaks : bytes list;
}
val strip_outside_parens : bytes -> bytes
val render_bop : bop -> bytes
val render_tterm : tterm -> bytes
val render_term : term -> bytes
val term_eq : term -> term -> bool
