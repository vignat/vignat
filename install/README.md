This folder contains patches and configuration files for dependencies of the Vigor toolchain, namely:
- DPDK patches
  - `bugfixes` fixes bugs found in DPDK
  - `clean` contains minor cleanups that do not affect correctness, only ease of verification
  - `config` patches the DPDK default config
  - `features` disables DPDK features that are hard to verify
- A minimalistic config file for `klee-uclibc`
