# Files

* expiring_map.tex - specification of a sample network data structure - expiring map
* coq/ - proofs for sample programs written in coq:
 * sqr.v - natural number square root coq implementation
 * sqr2.v - the same implementation with a more concise proof
 * sqrt.c - c implementation of square root. It reflects the Coq's implementation, so it is easy to proof equivalence. Use clightgen to generate sqrt.v (part of CompCert distribution)
 * sqrt.v - clightgen-generated file from sqrt.c
 * verif_sqrt.v - VST proof of equivalence of sqrt.v to sqr.v .
 * verif_sqrt2.v - an attempt to proof equivalence of sqrt.v to sqr2.v.

# Use
To make sure, that sqrt.c indeed corresponds to sqr.v which conforms the specification sqrt(n)^2 <= n < (sqrt(n)+1)^2, you will need [Coq](https://coq.inria.fr/), [Compcert](http://compcert.inria.fr/download.html) and [VST](http://vst.cs.princeton.edu/), [Proofgeneral](http://proofgeneral.inf.ed.ac.uk/).

To install coq and proofgeneral in Ubuntu, use 
```
    $ apt-get install coq proofgeneral
```
Or download it from the links, supplied above.
Compcert and VST are in the standard Ubunto repo, so you have to download, unpack and build them by hand.
