# Files

Here is a brief description of the contents of the project, which is essentially a collection of weakly connected artifacts. Please, look also for README.md files in the subdirectories.

* expiring_map.tex - specification of a sample network data structure - expiring map
* vst/ - proofs for sample programs written in coq using the VST, including a trivial mod-based (int->int) map.
* bench/ - a simple benchmark for the certified map implementation compating it with standard implementation: GNU g_hash_table and std::unordered_map.
* dafny/ - an unfinished implementation of the same map in the Dafny framework.
* frama-c/ - a Frama-C/WP partially-certified implementation.
* verifast/ - A complete map implementation, certified with VeriFast.
* nat/ - A sample DPDK nat-box implementation, as a use-case for a verified hash-map.

