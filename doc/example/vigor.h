#ifndef _VIGOR_H_INCLUDED_
#define _VIGOR_H_INCLUDED_

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

#ifndef bool
#define bool int
#define true 1
#define false 0
#endif


#define FOR_EVERY_RING_ELEMENT(i, begin, end, expr)       \
  for (int j = 0; j < (end + CAP - begin)%CAP; ++j)       \
  {                                                       \
    int i = (j+begin)%CAP;                                \
    expr;                                                 \
  }

#define ASSERT(cond) klee_assert(cond)
#define ASSUME(cond) klee_assume(cond)

#define SYMBOLIC(name) klee_int(name)
#define SYMBOLIC_RANGE(a, b, name) klee_range(a, b, name)
#define FILL_SYMBOLIC(addr, size, name) klee_make_symbolic(addr, size, name)

#define LOOP(cond) (cond & klee_induce_invariants())
#define VIGOR_CHECK(cond) ASSERT(cond)

#endif//KLEE_VERIFICATION

#endif//_VIGOR_H_INCLUDED_
