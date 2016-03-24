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
type ir = {
  preamble : bytes;
  free_vars : var_spec Core.Std.String.Map.t;
  arguments : var_spec Core.Std.String.Map.t;
  tmps : var_spec Core.Std.String.Map.t;
  cmplxs : var_spec Core.Std.String.Map.t;
  context_lemmas : tterm list;
  calls : bytes list;
  leaks : bytes list;
}
val strip_outside_parens : bytes -> bytes
val render_bop : bop -> bytes
val render_tterm : tterm -> bytes
val term_eq : term -> term -> bool
