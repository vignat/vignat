type c_type =
  | Ptr of c_type
  | Int
  | Uint32
  | Uint16
  | Uint8
  | Void
  | Str of bytes * (bytes * c_type) list
  | Ctm of bytes
  | Fptr of bytes
  | Bool
  | Sunknown
  | Uunknown
  | Unknown
val c_type_to_str : c_type -> bytes
type lemma = (string -> string list -> string)
val is_void : c_type -> bool
val get_pointee : c_type -> c_type
type fun_spec = {
  ret_type : c_type;
  arg_types : c_type list;
  lemmas_before : bytes list;
  lemmas_after : lemma list;
  leaks : bytes list;
}
val dmap_struct : c_type
val dchain_struct : c_type
val ext_key_struct : c_type
val int_key_struct : c_type
val flw_struct : c_type
val fun_types : fun_spec Core.Std.String.Map.t
