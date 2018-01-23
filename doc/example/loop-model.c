#include "loop-model.h"

void loop_iteration_begin(struct ring **r) {
  loop_invariant_consume(r);
  loop_invariant_produce(r);
}

void loop_iteration_end(struct ring **r) {
  loop_invariant_consume(r);
  loop_invariant_produce(r);
}

void loop_invariant_consume(struct ring **r) {
  klee_trace_ret();
  klee_trace_param_ptr(r, sizeof(struct ring*), "r");
}

void loop_invariant_produce(struct ring **r) {
  klee_trace_ret();
  klee_trace_param_ptr(r, sizeof(struct ring*), "r");
}
