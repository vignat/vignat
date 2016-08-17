module Sexp = Core.Std.Sexp
type bop = Eq | Le | Lt | Ge | Gt | Add | Sub | Mul | And
val __bop_of_sexp__ : Sexp.t -> bop
val bop_of_sexp : Sexp.t -> bop
val sexp_of_bop : bop -> Sexp.t
type ttype =
    Ptr of ttype
  | Sint32
  | Sint8
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
val __ttype_of_sexp__ : Sexp.t -> ttype
val ttype_of_sexp : Sexp.t -> ttype
val sexp_of_ttype : ttype -> Sexp.t
type term =
    Bop of bop * tterm * tterm
  | Apply of bytes * tterm list
  | Id of bytes
  | Struct of bytes * var_spec list
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
and var_spec = { name : bytes; value : tterm; }
val __term_of_sexp__ : Sexp.t -> term
val term_of_sexp : Sexp.t -> term
val __tterm_of_sexp__ : Sexp.t -> tterm
val tterm_of_sexp : Sexp.t -> tterm
val __var_spec_of_sexp__ : Sexp.t -> var_spec
val var_spec_of_sexp : Sexp.t -> var_spec
val sexp_of_term : term -> Sexp.t
val sexp_of_tterm : tterm -> Sexp.t
val sexp_of_var_spec : var_spec -> Sexp.t
val ttype_to_str : ttype -> bytes
val is_void : ttype -> bool
val get_pointee : ttype -> ttype
type fun_call_context = {
  pre_lemmas : bytes list;
  application : term;
  post_lemmas : bytes list;
  ret_name : bytes option;
  ret_type : ttype;
}
val __fun_call_context_of_sexp__ : Sexp.t -> fun_call_context
val fun_call_context_of_sexp : Sexp.t -> fun_call_context
val sexp_of_fun_call_context : fun_call_context -> Sexp.t
type hist_call_result = {
  args_post_conditions : var_spec list;
  ret_val : tterm;
}
val __hist_call_result_of_sexp__ : Sexp.t -> hist_call_result
val hist_call_result_of_sexp : Sexp.t -> hist_call_result
val sexp_of_hist_call_result : hist_call_result -> Sexp.t
type tip_result = {
  args_post_conditions : var_spec list;
  ret_val : tterm;
  post_statements : tterm list;
}
val __tip_result_of_sexp__ : Sexp.t -> tip_result
val tip_result_of_sexp : Sexp.t -> tip_result
val sexp_of_tip_result : tip_result -> Sexp.t
type hist_call = { context : fun_call_context; result : hist_call_result; }
val __hist_call_of_sexp__ : Sexp.t -> hist_call
val hist_call_of_sexp : Sexp.t -> hist_call
val sexp_of_hist_call : hist_call -> Sexp.t
type tip_call = { context : fun_call_context; results : tip_result list; }
val __tip_call_of_sexp__ : Sexp.t -> tip_call
val tip_call_of_sexp : Sexp.t -> tip_call
val sexp_of_tip_call : tip_call -> Sexp.t
type ir = {
  preamble : bytes;
  free_vars : var_spec Core.Std.String.Map.t;
  arguments : var_spec Core.Std.String.Map.t;
  tmps : var_spec Core.Std.String.Map.t;
  cmplxs : var_spec Core.Std.String.Map.t;
  context_assumptions : tterm list;
  hist_calls : hist_call list;
  tip_call : tip_call;
  export_point : bytes;
  finishing : bool;
}
val __ir_of_sexp__ : Sexp.t -> ir
val ir_of_sexp : Sexp.t -> ir
val sexp_of_ir : ir -> Sexp.t
val strip_outside_parens : bytes -> bytes
val render_bop : bop -> bytes
val render_tterm : tterm -> bytes
val render_term : term -> bytes
val term_eq : term -> term -> bool
val replace_term_in_term : term -> term -> term -> term
val replace_term_in_tterm : term -> term -> tterm -> tterm
val replace_term_in_tterms : term -> term -> tterm list -> tterm list
val call_recursively_on_tterm : (term -> term option) -> tterm -> tterm
val collect_nodes : (tterm -> 'a option) -> tterm -> 'a list
val term_contains_term : term -> term -> bool
val tterm_contains_term : tterm -> term -> bool
val tterms_contain_term : tterm list -> term -> bool
val is_const : term -> bool
val is_constt : tterm -> bool
