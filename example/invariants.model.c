#include "invariants.h"

void invariant_consume(struct cell* cp)
//@ requires cellp(cp, _);
//@ ensures true;
{
  //do nothing
}

void invariant_produce(struct cell** cpp)
//@ requires *cpp |-> _;
//@ ensures *cpp |-> ?cp &*& cellp(cp, _);
{
  //do nothing
}
