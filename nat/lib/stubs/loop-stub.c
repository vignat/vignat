#include <klee/klee.h>
#include "loop.h"


void loop_invariant_consume()
{
  klee_trace_ret();
}

void loop_invariant_produce()
{
  klee_trace_ret();
}

void loop_iteration_begin() {
  loop_invariant_consume();
  loop_invariant_produce();
}

void loop_iteration_end() {
  loop_invariant_consume();
  loop_invariant_produce();
}

void loop_enumeration_begin(int cnt)
{
  klee_trace_ret();
  klee_trace_param_i32(cnt, "cnt");
}

void loop_enumeration_end()
{
  klee_trace_ret();
}
