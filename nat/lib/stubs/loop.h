#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "lib/flow.h"

//@ #include "lib/predicates.gh"

/*@

predicate dmap_dchain_coherent(dmap<int_k,ext_k,flw> m, dchain ch) = true;

fixpoint int dochain_index_range(dchain ch);

predicate nat_flow_p(int_k ik, ext_k ek, flw fl, int index) =
   flow_p(fl, ik, ek) &*& ext_k_get_esp(ek) == 2747 + index;

predicate evproc_loop_invariant(struct DoubleMap* mp, struct DoubleChain *chp) =
          dmappingp<int_k,ext_k,flw>(?m, int_k_p, ext_k_p, flw_p, nat_flow_p,
                                     ?capacity, mp) &*&
          double_chainp(?ch, ?index_range, chp) &*&
          dmap_dchain_coherent(m, ch) &*&
          last_time(?t) &*&
          index_range == capacity;

lemma void coherent_dmap_used_dchain_allocated(dmap<int_k,ext_k,flw> m, dchain ch, int idx);
requires dmap_dchain_coherent(m, ch) &*& dmap_index_used_fp(m, idx) == true;
ensures dmap_dchain_coherent(m, ch) &*&
        dchain_allocated_index_fp(ch, idx) == true;

lemma void expire_preserves_coherent(dmap<int_k,ext_k,flw> m, dchain ch, uint32_t time);
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(dmap_erase_all_fp(m, dchain_get_expired_indexes_fp(ch, time)),
                             dchain_expire_old_indexes_fp(ch, time));

lemma void rejuvenate_preserves_coherent(dmap<int_k,ext_k,flw> m, dchain ch,
                                         int index, uint32_t time);
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, dchain_rejuvenate_fp(ch, index, time));

lemma void coherent_put_allocated_preserves_coherent
(dmap<int_k,ext_k,flw> m, dchain ch, int_k k1, ext_k k2, flw value);
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(dmap_put_fp(m, k1, k2,
                                         dchain_get_next_index_fp(ch),
                                         value),
                             dchain_take_next_index_fp(ch));

lemma void coherent_dchain_non_out_of_space_map_nonfull(dmap<int_k,ext_k,flw> m, dchain ch);
requires dmappingp<int_k,ext_k,flw>(m, ?a, ?b, ?c, ?d, ?cap, ?f) &*&
         dmap_dchain_coherent(m, ch) &*&
         dchain_out_of_space_fp(ch) == false;
ensures dmappingp<int_k,ext_k,flw>(m, a, b, c, d, cap, f) &*&
        dmap_dchain_coherent(m, ch) &*&
        dmap_size_fp(m) < cap;
@*/

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch);
//@ requires *m |-> ?mp &*& *ch |-> ?chp &*& evproc_loop_invariant(mp, chp);
//@ ensures *m |-> mp &*& *ch |-> chp;

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch);
//@ requires *m |-> ?mp &*& *ch |-> ?chp;
//@ ensures *m |-> mp &*& *ch |-> chp &*& evproc_loop_invariant(mp, chp);

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch);

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch);

void loop_enumeration_begin(int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end();
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
