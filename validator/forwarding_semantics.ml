open Core.Std
open Ir

let add_semantic_checks ir =
  if ir.complete_event_loop_iteration then
    {ir with
     arguments = {name = "bugaga"; value = {v = Undef; t = Boolean}} :: ir.Ir.arguments;
     Ir.semantic_checks = "assert true;"}
  else
    ir
