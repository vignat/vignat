type lemma = bytes -> bytes list -> (bytes -> bytes) -> bytes
type blemma = bytes list -> (bytes -> bytes) -> bytes
type leak_updater =
    bytes ->
    bytes list -> bytes Core.Std.String.Map.t -> bytes Core.Std.String.Map.t
val tx_l : bytes -> 'a -> 'b -> 'c -> bytes
val tx_bl : bytes -> 'a -> 'c -> bytes
val leak :
  bytes ->
  ?id:bytes ->
  'a -> 'b -> bytes Core.Std.String.Map.t -> bytes Core.Std.String.Map.t
val on_rez_nz_leak :
  bytes ->
  ?id:bytes ->
  bytes -> 'a -> bytes Core.Std.String.Map.t -> bytes Core.Std.String.Map.t
val remove_leak :
  bytes -> 'a -> 'b -> 'c Core.Std.String.Map.t -> 'c Core.Std.String.Map.t
val on_rez_nonzero : bytes -> bytes -> 'a -> 'b -> bytes
val on_rez_nz : ('a -> 'b -> bytes) -> bytes -> 'a -> 'b -> bytes

type fun_spec = {
  ret_type : Ir.ttype;
  arg_types : Ir.ttype list;
  lemmas_before : blemma list;
  lemmas_after : lemma list;
  leaks : leak_updater list;
}

module type Spec =
sig
  val preamble  : bytes
  val fun_types : fun_spec Core.Std.String.Map.t
  val fixpoints : Ir.tterm Core.Std.String.Map.t
end

val spec : (module Spec) option ref
