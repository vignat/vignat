type lemma = bytes -> bytes list -> bytes
type blemma = bytes list -> bytes
val tx_l : bytes -> 'a -> 'b -> bytes
val tx_bl : bytes -> 'a -> bytes
val on_rez_nonzero : bytes -> bytes -> 'a -> bytes
val on_rez_nz : ('a -> bytes) -> bytes -> 'a -> bytes
type map_key = Sint32 | Ext
val last_index_gotten : bytes ref
val last_index_key : map_key ref
val last_indexing_succ_ret_var : bytes ref
val gen_get_fp : bytes -> bytes
type fun_spec = {
  ret_type : Ir.ttype;
  arg_types : Ir.ttype list;
  lemmas_before : blemma list;
  lemmas_after : lemma list;
  leaks : bytes list;
}
val dmap_struct : Ir.ttype
val dchain_struct : Ir.ttype
val ext_key_struct : Ir.ttype
val int_key_struct : Ir.ttype
val flw_struct : Ir.ttype
val fun_types : fun_spec Core.Std.String.Map.t
