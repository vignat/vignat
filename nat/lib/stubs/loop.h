#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "lib/flow.h"

//@ #include "lib/predicates.gh"

//TODO: coerce this with the definition in rte_stubs.h
#define RTE_NUM_DEVICES 2

/*@

predicate dmap_dchain_coherent(dmap<int_k,ext_k,flw> m, dchain ch);

fixpoint int dochain_index_range(dchain ch);

fixpoint bool nat_int_fp(int_k ik, int index) {
    return 0 <= int_k_get_idid(ik) &&
           int_k_get_idid(ik) < RTE_NUM_DEVICES;
}

fixpoint bool nat_ext_fp(ext_k ek, int index) {
    return ext_k_get_esp(ek) == 2747 + index &&
           0 <= ext_k_get_edid(ek) &&
           ext_k_get_edid(ek) < RTE_NUM_DEVICES;
}


predicate evproc_loop_invariant(struct DoubleMap* mp, struct DoubleChain *chp,
                                uint32_t time) =
          dmappingp<int_k,ext_k,flw>(?m, int_k_p, ext_k_p, int_hash, ext_hash,
                                     flw_p, flow_p, flow_keys_offsets_fp,
                                     sizeof(struct flow), flw_get_ik, flw_get_ek,
                                     nat_int_fp, nat_ext_fp, ?capacity, mp) &*&
          double_chainp(?ch, chp) &*&
          dmap_dchain_coherent(m, ch) &*&
          last_time(time) &*&
          dchain_index_range_fp(ch) == capacity &*&
          capacity == MAX_FLOWS;

lemma void empty_dmap_dchain_coherent(int len);
requires true;
ensures dmap_dchain_coherent(empty_dmap_fp(len), empty_dchain_fp(len));

lemma void coherent_dmap_used_dchain_allocated(dmap<int_k,ext_k,flw> m, dchain ch, int idx);
requires dmap_dchain_coherent(m, ch) &*& dmap_index_used_fp(m, idx) == true;
ensures dmap_dchain_coherent(m, ch) &*&
        dchain_allocated_fp(ch, idx) == true;

lemma void expire_preserves_coherent(dmap<int_k,ext_k,flw> m, dchain ch, uint32_t time);
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(dmap_erase_all_fp(m, dchain_get_expired_indexes_fp(ch, time),
                                               flw_get_ik, flw_get_ek),
                             dchain_expire_old_indexes_fp(ch, time));

lemma void rejuvenate_preserves_coherent(dmap<int_k,ext_k,flw> m, dchain ch,
                                         int index, uint32_t time);
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, dchain_rejuvenate_fp(ch, index, time));

lemma void coherent_put_allocated_preserves_coherent
(dmap<int_k,ext_k,flw> m, dchain ch, int_k k1, ext_k k2,
 flw value, int ind, uint32_t t);
requires dmap_dchain_coherent(m, ch) &*& false == dchain_allocated_fp(ch, ind);
ensures dmap_dchain_coherent(dmap_put_fp(m, ind, value, flw_get_ik, flw_get_ek),
                             dchain_allocate_fp(ch, ind, t));

lemma void coherent_dchain_non_out_of_space_map_nonfull(dmap<int_k,ext_k,flw> m, dchain ch);
requires dmappingp<int_k,ext_k,flw>(m, ?a, ?b, ?c, ?d, ?e, ?g, ?h, ?i, ?j, ?k, ?l, ?n, ?cap, ?f) &*&
         dmap_dchain_coherent(m, ch) &*&
         dchain_out_of_space_fp(ch) == false;
ensures dmappingp<int_k,ext_k,flw>(m, a, b, c, d, e, g, h, i, j, k, l, n, cap, f) &*&
        dmap_dchain_coherent(m, ch) &*&
        dmap_size_fp(m) < cap;
@*/

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t time);
//@ requires *m |-> ?mp &*& *ch |-> ?chp &*& evproc_loop_invariant(mp, chp, time);
//@ ensures *m |-> mp &*& *ch |-> chp;

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch,
                            uint32_t *time);
//@ requires *m |-> ?mp &*& *ch |-> ?chp &*& *time |-> ?t;
/*@ ensures *m |-> mp &*& *ch |-> chp &*& *time |-> t &*&
            evproc_loop_invariant(mp, chp, t); @*/

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                          uint32_t time);

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch,
                        uint32_t time);

void loop_enumeration_begin(int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end();
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
