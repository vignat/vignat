#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "lib/flow.h"

//@ #include "lib/predicates.gh"

/*@

predicate dmap_dchain_coherent(dmap<int_k,ext_k> m, dchain ch) = true;

fixpoint int dochain_index_range(dchain ch);

predicate evproc_loop_invariant(struct DoubleMap* mp, struct DoubleChain *chp) =
          dmappingp<int_k,ext_k>(?m, int_k_p, ext_k_p, _,
                                 ?capacity, mp) &*&
          double_chainp(?ch, ?index_range, chp) &*&
          dmap_dchain_coherent(m, ch) &*&
          last_time(?t) &*&
          index_range == capacity;

@*/

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch);
//@ requires *m |-> ?mp &*& *ch |-> ?chp &*& evproc_loop_invariant(mp, chp);
//@ ensures *m |-> _ &*& *ch |-> _;

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
