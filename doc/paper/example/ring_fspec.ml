
open Core.Std
open Fspec_api

let packet_struct = Ir.Str ( "packet", ["port", Sint32] )
let ring_struct = Ir.Str ( "ring", [])

let fun_types =
  String.Map.of_alist_exn
    ["ring_create", {ret_type = Ptr ring_struct;
                     arg_types = [Sint32];
                     lemmas_before = [(fun _ _ ->
                       "//@ close packet_property(user_property);")];
                     lemmas_after = [];};
     "ring_full", {ret_type = Boolean;
                   arg_types = [Ptr ring_struct];
                   lemmas_before = [];
                   lemmas_after = [];};
     "ring_empty", {ret_type = Boolean;
                    arg_types = [Ptr ring_struct];
                    lemmas_before = [];
                    lemmas_after = [];};
     "ring_push_back", {ret_type = Void;
                        arg_types = [Ptr ring_struct;
                                     Ptr packet_struct];
                        lemmas_before = [(fun args _ ->
                             "//@ close packetp(" ^
                             (List.nth_exn args 1) ^
                             ", packet((" ^ (List.nth_exn args 1) ^
                             ")->port));\n";)];
                        lemmas_after = [(fun params ->
                             "//@ open packetp(" ^
                             (List.nth_exn params.args 1) ^
                             ", _);\n";)];};
     "ring_pop_front", {ret_type = Void;
                        arg_types = [Ptr ring_struct;
                                     Ptr packet_struct];
                        lemmas_before = [(fun args _ ->
                             "//@ close packetp(" ^
                             (List.nth_exn args 1) ^
                             ", packet((" ^ (List.nth_exn args 1) ^
                             ")->port));\n";)];
                        lemmas_after = [
                          (fun params ->
                             "//@ open packetp(" ^
                             (List.nth_exn params.args 1) ^
                             ", _);\n";);];};
     "loop_invariant_consume", {ret_type = Void;
                                arg_types = [Ptr (Ptr ring_struct)];
                                lemmas_before = [(fun args _ ->
                                    "//@ close loop_invariant(*" ^
                                    (List.nth_exn args 0) ^ ");")];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = [Ptr (Ptr ring_struct)];
                                lemmas_before = [];
                                lemmas_after = [
                                  tx_l "open loop_invariant(_);"];};
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

