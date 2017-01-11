type lemma_params = {
  ret_name : bytes;
  ret_val : bytes;
  args : bytes list;
  tmp_gen : bytes -> bytes;
  is_tip : bool;
}
type lemma = lemma_params -> bytes
type blemma = bytes list -> (bytes -> bytes) -> bytes
val tx_l : bytes -> 'a -> bytes
val tx_bl : bytes -> 'a -> 'b -> bytes
val on_rez_nonzero : bytes -> lemma_params -> bytes
val on_rez_nz : (lemma_params -> bytes) -> lemma_params -> bytes
type fun_spec = {
  ret_type : Ir.ttype;
  arg_types : Ir.ttype list;
  extra_ptr_types: (bytes * Ir.ttype) list;
  lemmas_before : blemma list;
  lemmas_after : lemma list;
}
module type Spec =
  sig
    val preamble : bytes
    val fun_types : fun_spec Core.Std.String.Map.t
    val fixpoints : Ir.tterm Core.Std.String.Map.t
    val boundary_fun : bytes
    val finishing_fun : bytes
    val eventproc_iteration_begin : bytes
    val eventproc_iteration_end : bytes
  val user_check_for_complete_iteration : bytes
  end
val spec : (module Spec) option ref
