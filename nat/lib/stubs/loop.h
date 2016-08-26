#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "lib/flow.h"
#include "lib/containers/array-lcc.h"

//@ #include "lib/predicates.gh"

#include "lib/coherence.h"

//TODO: coerce this with the definition in rte_stubs.h
#define RTE_NUM_DEVICES 2

/*@
fixpoint bool nat_int_fp(int_k ik, int index) {
    return 0 <= int_k_get_idid(ik) &&
           int_k_get_idid(ik) < RTE_NUM_DEVICES;
}

fixpoint bool nat_ext_fp(int start_port, ext_k ek, int index) {
    return ext_k_get_esp(ek) == start_port + index &&
           0 <= ext_k_get_edid(ek) &&
           ext_k_get_edid(ek) < RTE_NUM_DEVICES;
}


predicate evproc_loop_invariant(struct DoubleMap* mp, struct DoubleChain *chp,
                                struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                                struct lcore_conf* cur_lcc,
                                uint32_t time, int max_flows, int start_port) =
          dmappingp<int_k,ext_k,flw>(?m, int_k_p, ext_k_p, int_hash, ext_hash,
                                     flw_p, flow_p, flow_keys_offsets_fp,
                                     sizeof(struct flow), flw_get_ik, flw_get_ek,
                                     nat_int_fp, (nat_ext_fp)(start_port), mp) &*&
          double_chainp(?ch, chp) &*&
          dmap_dchain_coherent(m, ch) &*&
          arrp_lcc_acc(_, arr_lcc, lcore_id) &*&
          cur_lcc == arrp_the_missing_cell_lcc(arr_lcc, lcore_id) &*&
          lcore_id == 0 &*& //<-- We are verifying for a single core.
          some_lcore_confp(cur_lcc) &*&
          last_time(time) &*&
          dchain_high_fp(ch) <= time &*&
          dmap_cap_fp(m) == max_flows &*&
          max_flows < INT_MAX;

@*/

void loop_iteration_assumptions(struct DoubleMap** m, struct DoubleChain** ch,
                                struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                                struct lcore_conf* cur_lcc,
                                uint32_t time, int max_flows, int start_port);

void loop_iteration_assertions(struct DoubleMap** m, struct DoubleChain** ch,
                               struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                               struct lcore_conf* cur_lcc,
                               uint32_t time, int max_flows, int start_port);

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch,
                            struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                            struct lcore_conf* cur_lcc,
                            uint32_t time, int max_flows, int start_port);
/*@ requires *m |-> ?mp &*& *ch |-> ?chp &*&
             evproc_loop_invariant(mp, chp, arr_lcc, lcore_id, cur_lcc,
                                   time, max_flows, start_port); @*/
/*@ ensures *m |-> mp &*& *ch |-> chp &*&
            chars(arr_lcc->data,
                  sizeof(ARRAY_LCC_EL_TYPE)*ARRAY_LCC_CAPACITY, _); @*/

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch,
                            struct ArrayLcc* arr_lcc, unsigned int* lcore_id,
                            struct lcore_conf* cur_lcc,
                            uint32_t *time, int max_flows, int start_port);
/*@ requires *m |-> ?mp &*& *ch |-> ?chp &*&
             *lcore_id |-> _ &*&
             *time |-> _; @*/
/*@ ensures *m |-> mp &*& *ch |-> chp &*&
            *lcore_id |-> ?lcid &*&
            *time |-> ?t &*&
            evproc_loop_invariant(mp, chp, arr_lcc, lcid, cur_lcc,
                                  t, max_flows, start_port); @*/

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                          struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                          struct lcore_conf* cur_lcc,
                          uint32_t time, int max_flows, int start_port);

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch,
                        struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                        struct lcore_conf* cur_lcc,
                        uint32_t time, int max_flows, int start_port);

void loop_enumeration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                            struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                            struct lcore_conf* cur_lcc,
                            uint32_t time, int max_flows, int start_port,
                            int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end(struct DoubleMap** m, struct DoubleChain** ch,
                          struct ArrayLcc* arr_lcc, unsigned int lcore_id,
                          struct lcore_conf* cur_lcc,
                          uint32_t time, int max_flows, int start_port);
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
