frama-c -wp -wp-rte map.c -wp-prover why3:alt-ergo,why3:z3,coq -wp-script map.c.wp.script -then -report
