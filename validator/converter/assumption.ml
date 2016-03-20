
type cmp = Lt | Gt | Le | Ge | Eq

type term =
         | Int of int
         | Id of string
         | Bool of bool
         | Cmp of (cmp*term*term)
         | Not of term
         (* fun call is flattened to just an id *)


let cmp_op_to_string = (function
  | Lt -> "<"
  | Le -> "<="
  | Eq -> "="
  | Ge -> ">="
  | Gt -> ">")

let rec term_to_string = (function
      | Bool b -> if b then "true" else "false"
      | Int i -> string_of_int i
      | Id i -> i
      | Cmp (op, lhs, rhs) -> "(" ^ (term_to_string lhs) ^ ")" ^
                              (cmp_op_to_string op) ^ "(" ^
                              (term_to_string rhs) ^ ")"
      | Not t -> "!" ^ "(" ^ (term_to_string t) ^ ")")
