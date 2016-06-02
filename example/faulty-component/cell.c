#include <stdlib.h>
#include "cell.h"

struct cell {
  int* v;
};
/*@
  predicate cellp(struct cell* cp, option<int> x) =
    malloc_block_cell(cp) &*&
    switch(x) { case none: return cp->v |-> 0;
                case some(v): return cp->v |-> ?i &*&
                                     i != 0 &*&
                                     malloc_block_ints(i, 1) &*&
                                     *i |-> v;};
  @*/

struct cell* alloc()
//@ requires true;
//@ ensures result == 0 ? true : cellp(result, none);
{
  struct cell* cp = malloc(sizeof(struct cell));
  if (cp == 0) return 0;
  cp->v = 0;
  //@ close cellp(cp, none);
  return cp;
}

int full(struct cell* c)
//@ requires cellp(c, ?x);
//@ ensures (x != none ? result == 1 : result == 0) &*& cellp(c, x);
{
  //@ open cellp(c, x);
  return c->v != 0 ? 1 : 0;
  //@ close cellp(c, x);
}

void push(struct cell* c, int x)
//@ requires cellp(c, none);
//@ ensures cellp(c, some(x));
{
  //@ open cellp(c, none);
  c->v = malloc(sizeof(int));
  *c->v = x;
  //@ close cellp(c, some(x));
  return 1;
}

int pop(struct cell* c)
//@ requires cellp(c, some(?v));
//@ ensures cellp(c, none) &*& result == v;
{
  //@ open cellp(c, some(v));
  int rez = *c->v;
  free(c->v);
  c->v = 0;
  //@ close cellp(c, none);
  return rez;
}
