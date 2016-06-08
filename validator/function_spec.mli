type map_key = Int | Ext
val last_index_gotten : bytes ref
val last_index_key : map_key ref
val last_indexing_succ_ret_var : bytes ref
val gen_get_fp : bytes -> bytes
val dmap_struct : Ir.ttype
val dchain_struct : Ir.ttype
val ext_key_struct : Ir.ttype
val int_key_struct : Ir.ttype
val flw_struct : Ir.ttype
val fun_types : Fspec_api.fun_spec Core.Std.String.Map.t
val fixpoints : Ir.tterm Core.Std.String.Map.t
