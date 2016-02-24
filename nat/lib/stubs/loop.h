#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "lib/flow.h"

//@ #include "lib/predicates.gh"

/*@

predicate dmap_dchain_coherent(dmap<int_k,ext_k> m, dchain ch) = true;

fixpoint int dochain_index_range(dchain ch);

predicate evproc_loop_invariant() =
          dmappingp<int_k,ext_k>(?m, _, _, _,
                                 ?capacity, _) &*&
          double_chainp(?ch, ?index_range, _) &*&
          dmap_dchain_coherent(m, ch) &*&
          last_time(?t) &*&
          index_range == capacity;

@*/

void loop_invariant_consume();
//@ requires evproc_loop_invariant();
//@ ensures true;

void loop_invariant_produce();
//@ requires true;
//@ ensures evproc_loop_invariant();

void loop_iteration_begin();

void loop_iteration_end();

void loop_enumeration_begin(int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end();
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
