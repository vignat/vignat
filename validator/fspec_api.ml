open Core.Std
open Ir

(* Args: return variable name, return value, args, tmpemporary name generator. *)
type lemma = (string -> string -> string list -> (string -> string) -> string)
type blemma = (string list -> (string -> string) -> string)

let tx_l str = (fun _ _ _ _ -> "/*@ " ^ str ^ " @*/" )
let tx_bl str = (fun _ _ -> "/*@ " ^ str ^ " @*/" )


let on_rez_nonzero str = (fun rez_var _ _ _ ->
    "/*@ if(" ^ rez_var ^ "!=0) " ^ str ^ "@*/")

let on_rez_nz f = (fun rez_var _ args tmp_gen ->
    "/*@ if(" ^ rez_var ^ "!=0) " ^ (f args tmp_gen) ^ " @*/")

type fun_spec = {ret_type: ttype; arg_types: ttype list;
                 lemmas_before: blemma list; lemmas_after: lemma list;}

module type Spec =
sig
  val preamble  : string
  val fun_types : fun_spec Core.Std.String.Map.t
  val fixpoints : Ir.tterm Core.Std.String.Map.t
  val boundary_fun : string
  val finishing_fun : string
end

let spec : (module Spec) option ref = ref None
