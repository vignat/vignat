open Core.Std

let add_semantic_checks ir =
  ir (*{ir with Ir.semantic_checks = "assert true;"}*)
