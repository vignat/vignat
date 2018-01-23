type lemma_params = {
  ret_name : bytes;
  ret_val : bytes;
  args : bytes list;
  tmp_gen : bytes -> bytes;
  is_tip : bool;
  arg_types : Ir.ttype list;
  exptr_types : Ir.ttype Core.String.Map.t;
  ret_type : Ir.ttype;
}
type blemma_params = {
  args : bytes list;
  tmp_gen : bytes -> bytes;
  is_tip : bool;
  arg_types : Ir.ttype list;
  exptr_types : Ir.ttype Core.String.Map.t;
  ret_type : Ir.ttype;
}
type lemma = lemma_params -> bytes
type blemma = blemma_params -> bytes
val tx_l : bytes -> 'a -> bytes
val tx_bl : bytes -> 'a -> bytes
val on_rez_nonzero : bytes -> lemma_params -> bytes
val on_rez_nz : (lemma_params -> bytes) -> lemma_params -> bytes
val render_deep_assignment : Ir.eq_condition -> bytes
val deep_copy : Ir.var_spec -> bytes
type type_set = Static of Ir.ttype | Dynamic of (bytes * Ir.ttype) list
val stt : Ir.ttype list -> type_set list
val estt : ('a * Ir.ttype) list -> ('a * type_set) list
type fun_spec = {
  ret_type : type_set;
  arg_types : type_set list;
  extra_ptr_types : (bytes * type_set) list;
  lemmas_before : blemma list;
  lemmas_after : lemma list;
}
module type Spec =
  sig
    val preamble : bytes
    val fun_types : fun_spec Core.String.Map.t
    val fixpoints : Ir.tterm Core.String.Map.t
    val boundary_fun : bytes
    val finishing_fun : bytes
    val eventproc_iteration_begin : bytes
    val eventproc_iteration_end : bytes
    val user_check_for_complete_iteration : bytes
  end
val spec : (module Spec) option ref
