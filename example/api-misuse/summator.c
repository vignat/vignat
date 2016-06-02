/*
  This example demonstrates how contract compliance is
  enforced.

  Here we first extract a value from the cell, and then check
  if it were present or not. This will be detected by the
  validator, as at the moment of the 'pop' call, there
  is no guarantee, that the cell is 'full'.
 */
#include "net.h"
#include "cell.h"
#include "invariants.h"

int main() {
  struct cell* cp = alloc();
  if (cp == 0) return -1;
#ifdef KLEE_VERIFICATION
  invariant_consume(cp);
  invariant_produce(&cp);
#else //KLEE_VERIFICATION
  while(1) {
#endif//KLEE_VERIFICATION
    int* p = recv();
    if (p == 0) continue;
    int stored = pop(cp);
    if (full(cp)) {
      int sum = stored + *p;
      send(&sum);
    } else {
      push(cp, *p);
      //failure at this point will not be detected,
      //because it is not accounted for in the invariant.
    }
#ifdef KLEE_VERIFICATION
    invariant_consume(cp);
    invariant_produce(&cp);
#else //KLEE_VERIFICATION
  }
#endif//KLEE_VERIFICATION
}
