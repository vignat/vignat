type bop = Eq | Le | Lt | Ge | Gt
         | Add | Sub
         | And


type ttype = | Ptr of ttype
             | Sint32
             | Uint32
             | Uint16
             | Uint8
             | Void
             | Str of string * (string * ttype) list
             | Ctm of string
             | Fptr of string
             | Boolean
             | Sunknown
             | Uunknown
             | Unknown

type term = Bop of bop*tterm*tterm
          | Apply of string*tterm list
          | Id of string
          | Struct of string*(string * tterm) list
          | Int of int
          | Bool of bool
          | Not of tterm
          | Str_idx of tterm*string
          | Deref of tterm
          | Addr of tterm
          | Fptr of string
          | Cast of ttype*tterm
          | Undef
and tterm = {v:term; t:ttype}

let rec ttype_to_str = function
  | Ptr c_type -> ttype_to_str c_type ^ "*"
  | Sint32 -> "int" | Uint32 -> "uint32_t" | Uint16 -> "uint16_t"
  | Uint8 -> "uint8_t" | Void -> "void" | Str (name, _) -> "struct " ^ name
  | Ctm name -> name | Fptr name -> name ^ "*" | Boolean -> "bool" | Unknown -> "???"
  | Sunknown -> "s??" | Uunknown -> "u??"

let is_void = function | Void -> true | _ -> false

let get_pointee = function | Ptr t -> t | _ -> failwith "not a plain pointer"

type var_spec = {name: string; v:tterm}

type ir = {
  preamble:string;
  var_defs:string list;
}
