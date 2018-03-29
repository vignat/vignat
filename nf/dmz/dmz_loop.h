#ifndef DMZ_LOOP_H
#define DMZ_LOOP_H
#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "lib/flow.h"
#include "lib/coherence.h"
#include "lib/nf_time.h"

/*@
fixpoint bool dmz_int_fp(int_k ik, int index) {
    return 0 <= int_k_get_idid(ik) &&
           int_k_get_idid(ik) < RTE_MAX_ETHPORTS;
}

fixpoint bool dmz_ext_fp(int start_port, ext_k ek, int index) {
    return ext_k_get_esp(ek) == start_port + index &&
           0 <= ext_k_get_edid(ek) &&
           ext_k_get_edid(ek) < RTE_MAX_ETHPORTS;
}

  predicate dmz_loop_invariant(struct DoubleChain* int_chain,
                               struct DoubleChain* dmz_chain,
                               struct DoubleMap* int_map,
                               struct DoubleMap* dmz_map,
                               time_t time,
                               uint32_t max_flows) =
    double_chainp(?ic, int_chain) &*&
    double_chainp(?dc, dmz_chain) &*&
    dmappingp<int_k,ext_k,flw>(?im, int_k_p, ext_k_p, int_hash, ext_hash,
                               flw_p, flow_p, flow_keys_offsets_fp,
                               sizeof(struct flow), flw_get_ik, flw_get_ek,
                               dmz_int_fp, (dmz_ext_fp)(0), int_map) &*&
    dmappingp<int_k,ext_k,flw>(?dm, int_k_p, ext_k_p, int_hash, ext_hash,
                               flw_p, flow_p, flow_keys_offsets_fp,
                               sizeof(struct flow), flw_get_ik, flw_get_ek,
                               dmz_int_fp, (dmz_ext_fp)(0), dmz_map) &*&
    dmap_dchain_coherent(im, ic) &*&
    dmap_dchain_coherent(dm, dc) &*&
    last_time(time) &*&
    time >= 0 &*&
    dchain_high_fp(ic) <= time &*&
    dchain_high_fp(dc) <= time &*&
    dmap_cap_fp(im) == max_flows &*&
    dmap_cap_fp(dm) == max_flows;
  @*/

void dmz_loop_invariant_consume(struct DoubleChain** int_chain,
                                struct DoubleChain** dmz_chain,
                                struct DoubleMap** int_map,
                                struct DoubleMap** dmz_map,
                                time_t time,
                                uint32_t max_flows);
/*@ requires *int_chain |-> ?ic &*& *dmz_chain |-> ?dc &*&
             *int_map |-> ?im &*& *dmz_map |-> ?dm &*&
             dmz_loop_invariant(ic, dc, im, dm,
                                time, max_flows); @*/
/*@ ensures *int_chain |-> ic &*& *dmz_chain |-> dc &*&
            *int_map |-> im &*& *dmz_map |-> dm; @*/


void dmz_loop_invariant_produce(struct DoubleChain** int_chain,
                                struct DoubleChain** dmz_chain,
                                struct DoubleMap** int_map,
                                struct DoubleMap** dmz_map,
                                time_t* time,
                                uint32_t max_flows);
/*@ requires *int_chain |-> ?ic &*& *dmz_chain |-> ?dc &*&
             *int_map |-> ?im &*& *dmz_map |-> ?dm &*&
             *time |-> _; @*/
/*@ ensures *int_chain |-> ic &*& *dmz_chain |-> dc &*&
            *int_map |-> im &*& *dmz_map |-> dm &*&
            *time |-> ?t &*&
            dmz_loop_invariant(ic, dc, im, dm,
                               t, max_flows); @*/

void dmz_loop_iteration_begin(struct DoubleChain** int_chain,
                              struct DoubleChain** dmz_chain,
                              struct DoubleMap** int_map,
                              struct DoubleMap** dmz_map,
                              time_t time,
                              uint32_t max_flows);
/*@ requires true; @*/
/*@ ensures true; @*/

void dmz_loop_iteration_end(struct DoubleChain** int_chain,
                            struct DoubleChain** dmz_chain,
                            struct DoubleMap** int_map,
                            struct DoubleMap** dmz_map,
                            time_t time,
                            uint32_t max_flows);
/*@ requires true; @*/
/*@ ensures true; @*/

void dmz_loop_iteration_assumptions(struct DoubleChain** int_chain,
                                    struct DoubleChain** dmz_chain,
                                    struct DoubleMap** int_map,
                                    struct DoubleMap** dmz_map,
                                    time_t time,
                                    uint32_t max_flows);
/*@ requires true; @*/
/*@ ensures true; @*/

#endif
