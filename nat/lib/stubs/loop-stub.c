#include <klee/klee.h>
#include "loop.h"
#include "my-time-stub-control.h"
#include "containers/double-chain-stub-control.h"
#include "containers/double-map-stub-control.h"
#include "rte-stubs-control.h"


void loop_iteration_assumptions(struct DoubleMap** m, struct DoubleChain** ch,
                                uint32_t time, int max_flows, int start_port)
{
  rte_reset();
  dchain_reset(*ch, max_flows);
  dmap_reset(*m, max_flows);
}

void loop_iteration_assertions(struct DoubleMap** m, struct DoubleChain** ch,
                               uint32_t time, int max_flows, int start_port)
{
  
}

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t time, int max_flows, int start_port)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_i32(time, "time");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_i32(start_port, "start_port");
}

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t *time, int max_flows, int start_port)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_ptr(time, sizeof(uint32_t), "time");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_i32(start_port, "start_port");
  dchain_reset(*ch, max_flows);
  *time = restart_time();
}

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                          uint32_t time, int max_flows, int start_port) {
  loop_invariant_consume(m, ch, time, max_flows, start_port);
  loop_invariant_produce(m, ch, &time, max_flows, start_port);
}

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch,
                        uint32_t time, int max_flows, int start_port) {
  loop_invariant_consume(m, ch, time, max_flows, start_port);
  loop_invariant_produce(m, ch, &time, max_flows, start_port);
}

void loop_enumeration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t time, int max_flows, int start_port,
                            int cnt)
{
  (void)cnt;
  loop_invariant_consume(m, ch, time, max_flows, start_port);
  loop_invariant_produce(m, ch, &time, max_flows, start_port);
  //klee_trace_ret();
  //klee_trace_param_i32(cnt, "cnt");
}

void loop_enumeration_end(struct DoubleMap** m, struct DoubleChain** ch,
                          uint32_t time, int max_flows, int start_port)
{
  loop_invariant_consume(m, ch, time, max_flows, start_port);
  loop_invariant_produce(m, ch, &time, max_flows, start_port);
  //klee_trace_ret();
}
