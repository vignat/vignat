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
* Compcert:
```bash
    $ wget http://compcert.inria.fr/release/compcert-2.4.tgz
    $ tar -xf compcert-2.4.tgz
    $ cd compcert-24 && ./configure ia32-linux && make -j8
    $ export PATH=$PATH:$PWD
```
* VST:
```bash
    $ wget http://vst.cs.princeton.edu/download/vst-1.5.tgz
    $ tar -xf vst-1.5.tgz
    $ cd vst
```
See the BUILD_ORGANIZATION file in vst for instruction on how to build it. If `vst` is is in the same parent directory as `compcert-2.4`, then:
```bash
    $ echo "COMPCERT=../compcert-2.4" > CONFIGURE
    $ make -j8
```

Now you have to set up your proofgeneral. Add to your `~/.emacs` file:
```elisp
;; proofgeneral CoQ mode:
(setq vst-base-path (expand-file-name "--- /path/to/vst ---"))
(setq compcert-install-path (expand-file-name "--- /path/to/compcert ---"))

(setq coq-load-path `((,(concat vst-base-path "/msl") "msl")
                      (,(concat vst-base-path "/sepcomp") "sepcomp")
                      (,(concat vst-base-path "/veric") "veric")
                      (,(concat vst-base-path "/floyd") "floyd")
                      (,(concat vst-base-path "/progs") "progs")
                      (,compcert-install-path "compcert")))
```
Where `"--- /path/to/vst ---"` is a string, containing a path to the directory where you built vst, and `"--- /path/to/compcert ---"` is a string with a path to your compcert installation.

If everything is cone correctly, you should be able to verify the proof now. Run Proofgeneral:
```bash
    $ proofgeneral coq/verif_sqrt.v
```
On the first run, Coq will need to compile everything. Enter `coq-compile-before-require-toggle` command. For that press `M-x`(or Alt-Option + x ), and then type `coq-compile-before-require-toggle` into the emerged commandline. (Make sure to do it exactly once, since it is a toggle).
Use `next` button on the top panel (or `C-c C-n`), to go through the proof step-by-step. First step may take a long time up to hours, because, here Coq compiles everything it can reach.
   
