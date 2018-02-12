This folder contains patches and configuration files for dependencies of the Vigor toolchain, namely:
- DPDK patches
  - `bugfixes` fixes bugs found in DPDK
  - `clean` contains minor cleanups that do not affect correctness, only ease of verification
  - `config` patches the DPDK default config
  - `features` disables DPDK features that are hard to verify
- DPDK patches for the `ixgbe` driver:
  - `unknown_swfw_sync_bit` removes the usage of an undocumented bit in the SWFW_SYNC (a.k.a. GSSR) register
- A minimalistic config file for `klee-uclibc`
