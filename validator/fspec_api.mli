type lemma = bytes -> bytes -> bytes list -> (bytes -> bytes) -> bytes
type blemma = bytes list -> (bytes -> bytes) -> bytes
val tx_l : bytes -> 'a -> 'b -> 'c -> 'd -> bytes
val tx_bl : bytes -> 'a -> 'b -> bytes
val on_rez_nonzero : bytes -> bytes -> 'a -> 'b -> 'c -> bytes
val on_rez_nz : ('a -> 'b -> bytes) -> bytes -> 'c -> 'a -> 'b -> bytes
type fun_spec = {
  ret_type : Ir.ttype;
  arg_types : Ir.ttype list;
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
  end
val spec : (module Spec) option ref
