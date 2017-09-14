# VigNAT
This repository contains the VigNAT code together with the Vigor verification toolchain.

## Dependencies
### Unconditional dependencies
* DPDK-16.04
### Verification dependencies
* KLEE
* VeriFast

## How To Build VigNAT
## How To Run VigNAT
## How To Verify VigNAT


## Files

Here is a brief description of the contents of the project, which is essentially a collection of weakly connected artifacts. Please, look also for README.md files in the subdirectories.

* doc - contains all the documents/specs/justifications for Vigor approach
* example - contains a small example that demonstrates the Vigor approach. It is a more complete version of the example used for our paper.
* klee - a patched version of the [KLEE](https://klee.github.io) symbolic execution engine
* map-verification-attempts
* nf - contains the library of the verifiec Vigor data structures and all the NF involved in the projects, some of them are verified some are not
* validator - the validator, one of the steps in the Vigor approach.
* verifast - A patched version of the [VeriFast](https://github.com/verifast/verifast) theorem proover
* verification-outdated.docker - an outdated Docker config file that contains all the dependencies
