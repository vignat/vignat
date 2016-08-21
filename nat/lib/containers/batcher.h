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
  predicate batcherp(list<BATCHER_EL_TYPE> batch, struct Batcher* bat);
  predicate batcher_accp(struct Batcher* bat, int len);
  fixpoint BATCHER_EL_TYPE* batcher_contents(struct Batcher* bat);
  @*/

/**
   In-place initialization. Initializes the preallocated memory.

   @param bat_out - pointer to a preallocated memory for struct Batcher.
*/
void batcher_init(struct Batcher *bat_out);
//@ requires *bat_out |-> _;
//@ ensures batcherp(nil, bat_out);

/**
   Push an element into the batcher. The batcher must be non-full.

   @param bat - a pointer to the batcher.
   @param val - the value to push into the batcher.
 */
void batcher_push(struct Batcher *bat, BATCHER_EL_TYPE val);
//@ requires batcherp(?b, bat);
//@ ensures batcherp(cons(val, b), bat);

/**
   Get access to all the elements collected in the batcher so far. When you
   are done with processing the elements, you must call batcher_empty to prepare
   it for new pushes.

   @param bat - a pointer to the batcher.
   @param vals_out - output pointer to the 
   @param count_out - an output pointer to the total number of elements stored.
*/
void batcher_take_all(struct Batcher *bat,
                      BATCHER_EL_TYPE **vals_out, int *count_out);
//@ requires batcherp(?b, bat);
/*@ ensures batcher_accp(bat, length(b)) &*& *vals_out |-> ?vals &*&
            vals == batcher_contents(bat) &*&
            *count_out |-> length(b) &*& valsp(vals, length(b), b) &*&
            length(b) <= BATCHER_CAPACITY; @*/

void batcher_empty(struct Batcher *bat);
/*@ requires batcher_accp(bat, ?len) &*&
             vals(batcher_contents(bat), len, _); @*/
//@ ensures batcherp(nil, bat);

int batcher_full(struct Batcher *bat);
//@ requires batcherp(?b, bat);
/*@ ensures batcherp(b, bat) &*&
            result == (length(b) == BATCHER_CAPACITY ? 1 : 0); @*/

int batcher_is_empty(struct Batcher *bat);
//@ requires batcherp(?b, bat);
//@ ensures batcherp(b, bat) &*& result == (b == nil ? 1 : 0);

#endif//_BATCHER_H_INCLUDED_
