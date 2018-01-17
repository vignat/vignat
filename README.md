This repository contains the Vigor verification toolchain, along with the verified NAT ("VigNAT") and some experiments.


# Installation

Use the `install.sh` script to install all dependencies (in your working directory), or use the Dockerfile (`docker build . -t vignat`).


# Compilation

To build VigNAT, run

```bash
$ cd nf/vignat
$ make
```

This will compile and link VigNAT in the `build` directory. (Run it to be shown a help page)


# Verification

First step, verify the data structures (can be done any time):

```bash
$ cd nf/vignat
$ make verifast
```

Second step, symbolically execute the NAT to generate traces (can be done any time):

```bash
$ cd nf/vignat
$ make verifast
```

Third step, validate the generated traces (depends on the traces from the second step):

```bash
$ cd validator
$ make clean && ./test_all.sh ../nf/vignat/klee-last aaa ../nf nat_fspec.cmo
```


# Other information

The project is a collection of weakly connected artifacts. Subdirectories have their own README files.

* nf - contains the library of the verified Vigor data structures and all the NFs involved in the project, some of them are verified some are not
* validator - the validator, one of the steps in the Vigor approach.
* doc - contains all the documents/specs/justifications for Vigor approach
* doc/example - contains a small example that demonstrates the Vigor approach. It is a more complete version of the example used for our paper.
* doc/map-verification-attempts - old attempts to verify maps
