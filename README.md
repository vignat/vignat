* expiring_map.tex - specification of a sample network data structure - expiring map
* coq/ - proofs for sample programs written in coq:
 * sqr.v - natural number square root coq implementation
 * sqr2.v - the same implementation with a more concise proof
 * sqrt.c - c implementation of square root. It reflects the Coq's implementation, so it is easy to proof equivalence. Use lightcgen to generate sqrt.v (part of CompCert distribution)
 * verif_sqrt.v - VST proof of equivalence of sqrt.v to sqr.v .
 * verif_sqrt2.v - an attempt to proof equivalence of sqrt.v to sqr2.v.
