
type cmp = Lt | Gt | Le | Ge | Eq

type term =
         | Int of int
         | Id of string
         | Bool of bool
         | Cmp of (cmp*term*term)
         | Not of term
         | Call of (string*term list)


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
      | Not t -> "!" ^ "(" ^ (term_to_string t) ^ ")"
      | Call (fname, args) -> fname ^ "(" ^
                              (String.concat ", "
                                 (List.map term_to_string args)) ^
                              ")")


let rec term_eq a b =
  match (a,b) with
  | Int x, Int y -> x = y
  | Id x, Id y -> Core.Std.String.equal x y
  | Bool x, Bool y -> x = y
  | Cmp (acmp,alhs,arhs), Cmp (bcmp,blhs,brhs) ->
    acmp = bcmp && (term_eq alhs blhs) && (term_eq arhs brhs)
  | Not x, Not y -> term_eq x y
  | _, _ -> false
