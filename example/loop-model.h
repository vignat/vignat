#ifndef _LOOP_MODEL_H_INCLUDED_
#define _LOOP_MODEL_H_INCLUDED_

#include "user-params.h"

#include "ring.h"

/*@
  predicate loop_invariant(struct ring* rp) =
    ringp(rp, packet_constraints_fp, _, RING_CAPACITY);
  @*/

void loop_invariant_consume(struct ring **r);
//@ requires *r |-> ?rp &*& loop_invariant(rp);
//@ ensures *r |-> rp;

void loop_invariant_produce(struct ring **r);
//@ requires *r |-> ?rp;
//@ ensures *r |-> rp &*& loop_invariant(rp);

void loop_iteration_begin(struct ring **r);
void loop_iteration_end(struct ring **r);


#endif//_LOOP_MODEL_H_INCLUDED_
