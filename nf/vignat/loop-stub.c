#include <klee/klee.h>
#include "loop.h"
#include "lib/stubs/my-time-stub-control.h"
#include "lib/stubs/containers/double-chain-stub-control.h"
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/stubs/rte-stubs-control.h"

//TODO: this is a copy-paste from array_lcc.h and other array headers
//. Move it to a separate file.

void loop_iteration_assumptions(struct DoubleMap** m, struct DoubleChain** ch,
                                unsigned int lcore_id,
                                uint32_t time, int max_flows, int start_port)
{
  rte_reset();
  dchain_reset(*ch, max_flows);
  dmap_reset(*m, max_flows);
}

void loop_iteration_assertions(struct DoubleMap** m, struct DoubleChain** ch,
                               unsigned int lcore_id,
                               uint32_t time, int max_flows, int start_port)
{

}

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch,
                            unsigned int lcore_id,
                            uint32_t time, int max_flows, int start_port)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_i32(lcore_id, "lcore_id");
  //ARRAY_LCC_EL_TRACE_ARG_BREAKDOWN(cur_lcc);
  klee_trace_param_i32(time, "time");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_i32(start_port, "start_port");
}

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch,
                            unsigned int* lcore_id,
                            uint32_t *time, int max_flows, int start_port)
{
  klee_trace_ret();
  klee_trace_param_ptr(m, sizeof(struct DoubleMap*), "m");
  klee_trace_param_ptr(ch, sizeof(struct DoubleChain*), "ch");
  klee_trace_param_ptr(lcore_id, sizeof(unsigned int), "lcore_id");
  //ARRAY_LCC_EL_TRACE_ARG_BREAKDOWN(cur_lcc);
  klee_trace_param_ptr(time, sizeof(uint32_t), "time");
  klee_trace_param_i32(max_flows, "max_flows");
  klee_trace_param_i32(start_port, "start_port");
  dchain_reset(*ch, max_flows);
  *time = restart_time();
}

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                          unsigned int lcore_id,
                          uint32_t time, int max_flows, int start_port) {
  loop_invariant_consume(m, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, ch, &lcore_id,
                         &time, max_flows, start_port);
}

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch,
                        unsigned int lcore_id,
                        uint32_t time, int max_flows, int start_port) {
  loop_invariant_consume(m, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, ch, &lcore_id,
                         &time, max_flows, start_port);
}

void loop_enumeration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                            unsigned int lcore_id,
                            uint32_t time, int max_flows, int start_port,
                            int cnt)
{
  (void)cnt;
  loop_invariant_consume(m, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, ch, &lcore_id,
                         &time, max_flows, start_port);
  //klee_trace_ret();
  //klee_trace_param_i32(cnt, "cnt");
}

void loop_enumeration_end(struct DoubleMap** m, struct DoubleChain** ch,
                          unsigned int lcore_id,
                          uint32_t time, int max_flows, int start_port)
{
  loop_invariant_consume(m, ch, lcore_id,
                         time, max_flows, start_port);
  loop_invariant_produce(m, ch, &lcore_id,
                         &time, max_flows, start_port);
  //klee_trace_ret();
}
