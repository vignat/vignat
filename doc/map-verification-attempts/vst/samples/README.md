# Files

 * sqr.v - natural number square root coq implementation
 * sqr2.v - the same implementation with a more concise proof
 * sqrt.c - c implementation of square root. It reflects the Coq's implementation, so it is easy to proof equivalence. Use clightgen to generate sqrt.v (part of CompCert distribution)
 * sqrt.v - clightgen-generated file from sqrt.c
 * verif_sqrt.v - VST proof of equivalence of sqrt.v to sqr.v 
 * verif_sqrt2.v - an attempt to proof equivalence of sqrt.v to sqr2.v
 * assoc.c - simple circular array implementation
 * assoc.v - the automatic clightgen translation of assoc.c into Coq IR
 * assoc_spec.v - CoQ high level specification, middle level implementation and correspondence proof
 * verif\_assoc.v - VST specification and proof of equality of assoc.v and assoc_spec.v's middle level implementation
 * intro.v - A couple of examples, demonstrating that `intro.` tactic can not be performed automatically by the `Proof.` command.
