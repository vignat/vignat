#include "dmz_loop.h"
#include "lib/stubs/time_stub_control.h"
#include "lib/stubs/containers/double-chain-stub-control.h"
#include "lib/stubs/containers/double-map-stub-control.h"

#include <klee/klee.h>


void dmz_loop_invariant_consume(struct DoubleChain** int_chain,
                                struct DoubleChain** dmz_chain,
                                struct DoubleMap** int_map,
                                struct DoubleMap** dmz_map,
                                time_t time,
                                uint32_t max_flows)
/*@ requires *int_chain |-> ?ic &*& *dmz_chain |-> ?dc &*&
             *int_map |-> ?im &*& *dmz_map |-> ?dm &*&
             dmz_loop_invariant(ic, dc, im, dm,
                                time, max_flows); @*/
/*@ ensures *int_chain |-> ?ic &*& *dmz_chain |-> ?dc &*&
            *int_map |-> ?im &*& *dmz_map |-> ?dm; @*/
{
	klee_trace_param_ptr(int_chain, sizeof(struct DoubleChain*), "int_chain");
	klee_trace_param_ptr(dmz_chain, sizeof(struct DoubleChain*), "dmz_chain");
	klee_trace_param_ptr(int_map, sizeof(struct DoubleChain*), "int_map");
	klee_trace_param_ptr(dmz_map, sizeof(struct DoubleChain*), "dmz_map");
	klee_trace_param_i64(time, "time");
	klee_trace_param_u32(max_flows, "max_flows");
}


void dmz_loop_invariant_produce(struct DoubleChain** int_chain,
                                struct DoubleChain** dmz_chain,
                                struct DoubleMap** int_map,
                                struct DoubleMap** dmz_map,
                                time_t* time,
                                uint32_t max_flows)
/*@ requires *int_chain |-> ?ic &*& *dmz_chain |-> ?dc &*&
             *int_map |-> ?im &*& *dmz_map |-> ?dm &*&
             *time |-> _; @*/
/*@ ensures *int_chain |-> ?ic &*& *dmz_chain |-> ?dc &*&
            *int_map |-> ?im &*& *dmz_map |-> ?dm &*&
            *time |-> ?t &*&
            dmz_loop_invariant(ic, dc, im, dm,
                               t, max_flows); @*/
{
	klee_trace_param_ptr(int_chain, sizeof(struct DoubleChain*), "int_chain");
	klee_trace_param_ptr(dmz_chain, sizeof(struct DoubleChain*), "dmz_chain");
	klee_trace_param_ptr(int_map, sizeof(struct DoubleChain*), "int_map");
	klee_trace_param_ptr(dmz_map, sizeof(struct DoubleChain*), "dmz_map");
	klee_trace_param_ptr(time, sizeof(struct DoubleChain*), "time");
	klee_trace_param_u32(max_flows, "max_flows");
	dchain_reset(*int_chain, max_flows);
	dchain_reset(*dmz_chain, max_flows);
	*time = restart_time();
}

void dmz_loop_iteration_begin(struct DoubleChain** int_chain,
                              struct DoubleChain** dmz_chain,
                              struct DoubleMap** int_map,
                              struct DoubleMap** dmz_map,
                              time_t time,
                              uint32_t max_flows)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	dmz_loop_invariant_consume(int_chain, dmz_chain, int_map, dmz_map, time, max_flows);
	dmz_loop_invariant_produce(int_chain, dmz_chain, int_map, dmz_map, &time, max_flows);
}

void dmz_loop_iteration_end(struct DoubleChain** int_chain,
                            struct DoubleChain** dmz_chain,
                            struct DoubleMap** int_map,
                            struct DoubleMap** dmz_map,
                            time_t time,
                            uint32_t max_flows)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	dmz_loop_invariant_consume(int_chain, dmz_chain, int_map, dmz_map, time, max_flows);
	dmz_loop_invariant_produce(int_chain, dmz_chain, int_map, dmz_map, &time, max_flows);
}

void dmz_loop_iteration_assumptions(struct DoubleChain** int_chain,
                                    struct DoubleChain** dmz_chain,
                                    struct DoubleMap** int_map,
                                    struct DoubleMap** dmz_map,
                                    time_t time,
                                    uint32_t max_flows)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	dchain_reset(*int_chain, max_flows);
	dchain_reset(*dmz_chain, max_flows);
	dmap_reset(*int_map, max_flows);
	dmap_reset(*dmz_map, max_flows);
}
