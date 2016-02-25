#include <klee/klee.h>
#include "loop.h"


void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
}

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
}

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch) {
  loop_invariant_consume(m, ch);
  loop_invariant_produce(m, ch);
}

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch) {
  loop_invariant_consume(m, ch);
  loop_invariant_produce(m, ch);
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
