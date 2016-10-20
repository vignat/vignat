
open Core.Std
open Fspec_api

let packet_struct = Ir.Str ( "packet", ["port", Sint32] )
let ring_struct = Ir.Str ( "ring", [])

let fun_types =
  String.Map.of_alist_exn
    ["ring_create", {ret_type = Ptr ring_struct;
                     arg_types = [];
                     lemmas_before = [];
                     lemmas_after = [];};
     "ring_full", {ret_type = Bool;
                   arg_types = [Ptr ring_struct];
                   lemmas_before = [];
                   lemmas_after = [];};
     "ring_empty", {ret_type = Bool;
                    arg_types = [Ptr ring_struct];
                    lemmas_before = [];
                    lemmas_after = [];};
     "ring_push_back", {ret_type = Void;
                        arg_types = [Ptr ring_struct;
                                     Ptr packet_struct];
                        lemmas_before = [];
                        lemmas_after = [];};
     "ring_pop_front", {ret_type = Void;
                        arg_types = [Ptr ring_struct;
                                     Ptr packet_struct];
                        lemmas_before = [];
                        lemmas_after = [];};
    ]

let fixpoints = String.Map.empty

module Iface : Fspec_api.Spec =
struct
  let preamble = (In_channel.read_all "preamble.tmpl")
  let fun_types = fun_types
  let fixpoints = fixpoints
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

