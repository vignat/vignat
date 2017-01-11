open Core.Std
open Ir

type lemma_params = {ret_name: string; ret_val: string;
                     args: string list; tmp_gen: string -> string;
                     is_tip: bool}

(* Args: return variable name, return value, args, tmpemporary name generator. *)
type lemma = (lemma_params -> string)
type blemma = (string list -> (string -> string) -> string)

let tx_l str = (fun _ -> "/*@ " ^ str ^ " @*/" )
let tx_bl str = (fun _ _ -> "/*@ " ^ str ^ " @*/" )


let on_rez_nonzero str = (fun params ->
    "/*@ if(" ^ params.ret_name ^ "!=0) " ^ str ^ "@*/")

let on_rez_nz f = (fun params ->
    "/*@ if(" ^ params.ret_name ^ "!=0) " ^ (f params) ^ " @*/")

type fun_spec = {ret_type: ttype; arg_types: ttype list;
                 extra_ptr_types: (string * ttype) list;
                 lemmas_before: blemma list; lemmas_after: lemma list;}

module type Spec =
sig
  val preamble  : string
  val fun_types : fun_spec Core.Std.String.Map.t
  val fixpoints : Ir.tterm Core.Std.String.Map.t
  val boundary_fun : string
  val finishing_fun : string
  val eventproc_iteration_begin : string
  val eventproc_iteration_end : string
end

let spec : (module Spec) option ref = ref None
