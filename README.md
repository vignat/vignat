This repository contains the Vigor verification toolchain, along with the verified NAT ("VigNAT") and some experiments.

**For the version of the code presented at SIGCOMM 2017, use the `sigcomm17` branch.**

**For the version of the code presented at SIGCOMM 2018 KBNets, use the `kbnets18` branch.**
The main files of interest for this version are the patches in `install/`, and the stubs in `lib/stubs/`.


# Dependencies

Our dependencies, in the same GitHub organization, are modified versions of [KLEE](https://github.com/vignat/klee),
[KLEE-uClibc](https://github.com/vignat/klee-uclibc), and [VeriFast](https://github.com/vignat/verifast).


# Installation

### With Docker

Run `install-docker.sh`, which will create a Docker image and launch a container with the Vigor toolchain pre-installed.

### On your own machine

Run `install.sh`, which will install the Vigor toolchain and create a file named `paths.sh` containing all necessary environment variables
(which is automatically added to your `~/.profile`).


# Compilation, Execution, Verification

```bash
# Compile VigNAT
$ cd nf/vignat
$ make

# Run it (this will print a help message
$ ./build/nat

# Verify the data structures (can be done at any time)
$ make verifast

# Symbolically execute VigNAT to generate traces
$ make verify

# Verify the traces
$ cd ../../validator
$ make validate-nat
```


# Other information

Subdirectories have their own README files.

* nf - contains the library of the verified Vigor data structures and all the NFs involved in the project, some of them are verified some are not
* validator - the validator, one of the steps in the Vigor approach
* install - patches and config files for the Vigor toolchain dependencies
* doc - contains all the documents/specs/justifications for Vigor approach
* doc/example - contains a small example that demonstrates the Vigor approach. It is a more complete version of the example used for our paper
* doc/map-verification-attempts - old attempts to verify maps
