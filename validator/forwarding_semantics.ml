open Core.Std
open Ir

let put_markers ir =
  let new_lemmas fname post_lemmas =
    if String.equal fname "received_packet" then
      "a_packet_received = true;\n" :: post_lemmas
    else if String.equal fname "send_single_packet" then
      "a_packet_sent = true;\n" :: post_lemmas
    else
      post_lemmas
  in
  let marker_in_call (h_call : hist_call) : hist_call =
       match h_call.context.application with
       | Apply (fname,_) ->
         {h_call with
          context = {h_call.context with
                     post_lemmas = new_lemmas fname h_call.context.post_lemmas}}
       | _ -> failwith "application must be in the form Apply ..."
  in
  {ir with
   hist_calls = List.map ir.hist_calls ~f:marker_in_call}

let add_semantic_checks ir =
  if ir.complete_event_loop_iteration then
    let ir = put_markers ir in
    {ir with
     arguments = {name = "a_packet_received";
                  value = {v = Bool false; t = Boolean}} ::
                 {name = "a_packet_sent";
                  value = {v = Bool false; t = Boolean}} ::
                 ir.Ir.arguments;
     Ir.semantic_checks =
       "if (a_packet_received) { assert true == a_packet_sent; }"}
  else
    ir
