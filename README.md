# VigNAT
This repository contains the VigNAT code together with the Vigor verification toolchain.

## Dependencies
### Unconditional dependencies
* DPDK-16.04
### Verification dependencies
* [patched](https://github.com/vignat/klee) KLEE
* [patched](https://github.com/vignat/verifast) VeriFast

## The Docker image
We gathered all the configuration instructions into a [dockerfile](https://docs.docker.com/engine/reference/builder/) `verification.docker`, that you can conveniently build with

```bash
$ build -f verification.docker -t vignat .
```

This file also serves as a reference if you want to configure your real machine such that it can build and run Vigor. Just look for the `RUN` instructions in `verification.docker` and execute them on your ubuntu 14.04 machine. Once you built the docker image you can run a container with

```bash
$ docker run -it vignat
```

### Build the NAT
To build VigNAT, run
```bash
$ cd nf/vignat
$ make
```
This will compile and link VigNAT in the `build` directory. See `nf/vignat/testbed` for hints how to run it.
### Verify the NAT
Vigor approach consists of three steps:
1. Verification of the VigLib datastructures with theorem proving by running VeriFast on the annotated code.
2. Verification of the VigNAT safety with symbolic execution using KLEE.
3. Validation of the symbolic models used in the previous step against the formal contracts, and verificaiton against a semantic property formulated in `validator/forwarding_property.tmpl`.
First step relies only on the formal contracts for the datastructures and can be performed at any time independently.
The other two steps are dependent.
The last step works with symbolic call traces produced in the second step, so they should be run in order.
#### Theorem proving
```bash
$ cd nf/vignat
$ make verifast
```
#### Symbolic execution
```bash
$ cd nf/vignat
$ make verify
```
#### Validation
```bash
$ cd validator
$ ./test_all.sh ../nf/vignat/klee-last aaa ../nf nat_fspec.cmo
```


## Files

Here is a brief description of the contents of the project, which is essentially a collection of weakly connected artifacts. Please, look also for README.md files in the subdirectories.

* verification.docker - A Docker config file that contains full instructions to setup proper build and verificaiton environment for VigNAT
* doc - contains all the documents/specs/justifications for Vigor approach
* example - contains a small example that demonstrates the Vigor approach. It is a more complete version of the example used for our paper.
* klee - a patched version of the [KLEE](https://klee.github.io) symbolic execution engine
* map-verification-attempts
* nf - contains the library of the verifiec Vigor data structures and all the NF involved in the projects, some of them are verified some are not
* validator - the validator, one of the steps in the Vigor approach.
* verifast - A patched version of the [VeriFast](https://github.com/verifast/verifast) theorem proover
