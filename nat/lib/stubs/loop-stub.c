#include <klee/klee.h>
#include "loop.h"
#include "my-time-stub-control.h"


void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t time)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_i32(time, "time");
}

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t *time)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_ptr(time, sizeof(uint32_t), "time");
}

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                          uint32_t time) {
  loop_invariant_consume(m, ch, time);
  loop_invariant_produce(m, ch, &time);
}

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch,
                        uint32_t time) {
  loop_invariant_consume(m, ch, time);
  loop_invariant_produce(m, ch, &time);
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
