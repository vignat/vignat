# Hardware testbench

This folder contains the scripts necessary to benchmark VigNAT, Linux's NAT (NetFilter),
and any other DPDK-based software obeying VigNAT's public parameters "API", such as the provided `nop` and `unverified-nat` applications.

## Hardware setup

3 machines are required, each with an interface connected to the outside world and an associated hostname.  
All machines must be able to talk to each other by going through the outside world.  
As VigNAT is a DPDK-based app, the machines must have DPDK-compatible NICs.

The 1st machine is the tester, the 2nd is the NAT, and the 3rd is the server.  
There must be 2 connections between tester and NAT, and 1 connection between NAT and server.

## Software setup

Create an SSH key on the NAT and add its public key to the tester and server, as the scripts use SSH extensively.

Edit the `config.sh` file to set the machines' names and addresses.

**[NOTE: For now, you must also edit `pktgen/provision-rr.lua` and `pktgen/find-breaking-point-mf.lua` to set the machine addresses. Sorry!]**

## Running benchmarks

Benchmarks are run from the NAT machine.

The single entry point to all benchmarks is `bench.sh`. It takes two arguments.  
The first argument is either `netfilter` or the path to a VigNAT-like app.  
The second argument is the scenario, one of:  
- `1p` to measure maximal throughput with <1% loss;
- `loopback` to measure throughput;
- `rr` to measure two-way latency;
- `passthrough` to measure two-way latency _if testing an L2 forwarder_, such as the provided DPDK no-op.

The script outputs a `.results` file with the results. When testing a VigNAT-like app, a `.log` file will also be generated containing the standard output of the app.

## Configuring benchmarks

The following files contain benchmark parameters:
- `bench/latency.sh` contains the numbers of flows in the two-way latency benchmarks, and some waiting related to the expiration time;
- `pktgen/provision-rr.lua` contains the other parameters for the two-way latency benchmarks;
- `pktgen/find-breaking-point-mf.lua` contains all parameters for the throughput benchmarks;
- `bench.sh` contains the parameters passed to the VigNAT-like apps: expiration time, max flows, and starting port.

*NOTE*: The provided DPDK non-verified NAT automatically rounds the max flows up to a power of 2, as required by DPDK's hash table.

*NOTE*: Do not set the starting port to 0, as many servers do not like this at all, including Netperf's server which is used for measurements.

## Internals

- `config.sh` contains the configuration values; all other scripts begin by sourcing it.
- `clean.sh` cleans all machines, killing benchmark software that is already running and unbinding all network interfaces of the tester and NAT from both Linux and DPDK. (The per-machine scripts are in the `clean/` folder)
- `init-machines.sh` initializes all machines, cloning all scripts from the NAT to the tester and server then installing the software used for benchmarks if necessary. (The individual scripts and their helpers are in the `init-machines/` folder)
- `init-network.sh` initializes the network configuration by binding the necessary ports to DPDK or Linux as needed, setting up L2 and L3 routing tables, and configuring NetFilter if required. It takes two arguments, the scenario (same as `bench.sh`, except that `1p` does not exist at this level, only `loopback`), and the app kind to run on the NAT, either `dpdk` or `netfilter`. (The individual scripts and their helpers are in the `init-network-*/` folders)
- `bench.sh` ties it all together, using utilities defined in the `bench/` folder as well as DPDK-Pktgen utilities from the `pktgen/` folder.
