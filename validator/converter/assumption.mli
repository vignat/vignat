type cmp = Lt | Gt | Le | Ge | Eq
type term =
    Int of int
  | Id of bytes
  | Bool of bool
  | Cmp of (cmp * term * term)
  | Not of term
  | Call of (bytes * term list)
val cmp_op_to_string : cmp -> bytes
val term_to_string : term -> bytes
val term_eq : term -> term -> bool
