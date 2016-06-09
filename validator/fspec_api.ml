open Core.Std
open Ir

type lemma = (string -> string list -> (string -> string) -> string)
type blemma = (string list -> (string -> string) -> string)
type leak_updater = (string -> string list ->
                     string String.Map.t -> string String.Map.t)

let tx_l str = (fun _ _ _ -> "/*@ " ^ str ^ " @*/" )
let tx_bl str = (fun _ _ -> "/*@ " ^ str ^ " @*/" )


let leak str ?(id=str) = (fun _ _ leaks ->
    String.Map.add leaks ~key:id ~data:("/*@ leak " ^ str ^ ";@*/"))

let on_rez_nz_leak str ?(id=str) = (fun rez_var _ leaks ->
    String.Map.add leaks ~key:id ~data:("/*@ if(" ^ rez_var ^
                                        "!=0) leak " ^ str ^ ";@*/"))

let remove_leak id = (fun _ _ leaks ->
    String.Map.remove leaks id)

let on_rez_nonzero str = (fun rez_var _ _ ->
    "/*@ if(" ^ rez_var ^ "!=0) " ^ str ^ "@*/")

let on_rez_nz f = (fun rez_var args tmp_gen ->
    "/*@ if(" ^ rez_var ^ "!=0) " ^ (f args tmp_gen) ^ " @*/")

type fun_spec = {ret_type: ttype; arg_types: ttype list;
                 lemmas_before: blemma list; lemmas_after: lemma list;
                 leaks: leak_updater list;}

module type Spec =
sig
  val preamble  : string
  val fun_types : fun_spec Core.Std.String.Map.t
  val fixpoints : Ir.tterm Core.Std.String.Map.t
end

let spec = ref None
