#ifndef _BATCHER_H_INCLUDED_
#define _BATCHER_H_INCLUDED_

#include "lib/static-component-params.h"

#ifndef BATCHER_EL_TYPE
#  error "Must define the batcher element type."
#endif//BATCHER_EL_TYPE

#ifndef BATCHER_CAPACITY
#  error "Must define the batcher capacity."
#endif// BATCHER_CAPACITY

struct Batcher
{
  BATCHER_EL_TYPE batch[BATCHER_CAPACITY];
  int len;
};

/*@
  predicate batcherp(list<BATCHER_EL_TYPE> batch, struct Batcher* bat_out);
  @*/

// In-place initialization.
void batcher_init(struct Batcher *bat_out);
//@ requires *bat_out |-> _;
//@ ensures batcherp(nil, bat_out);

void batcher_push(struct Batcher *bat, BATCHER_EL_TYPE val);
//@ requires batcherp(?b, bat);
//@ ensures batcherp(cons(val, b), bat);

void batcher_take_all(struct Batcher *bat,
                      BATCHER_EL_TYPE **vals_out, int *count_out);
//@ requires batcherp(?b, bat);
/*@ ensures batcherp(nil, bat) &*& *vals_out |-> ?vals &*&
            *count_out |-> length(b) &*& vals[0..length(b)] |-> b; @*/

int batcher_full(struct Batcher *bat);
//@ requires batcherp(?b, bat);
/*@ ensures batcherp(b, bat) &*&
            result == (length(b) == BATCHER_CAPACITY ? 1 : 0); @*/

int batcher_empty(struct Batcher *bat);
//@ requires batcherp(?b, bat);
//@ ensures batcherp(b, bat) &*& result == (b == nil ? 1 : 0);

#endif//_BATCHER_H_INCLUDED_
