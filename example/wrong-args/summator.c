/* This version does not check the faulure
   to allocate the cell, so it may pass an
   uninitialized pointer to the function full, which
   does not anticipate this.

   The symbolic execution itself will not caught it,
   because it does not use the cell pointer argument,
   but the validator will notice the abscence of the
   corresponding predicate.
*/
#include "net.h"
#include "cell.h"
#include "invariants.h"

int main() {
  struct cell* cp = alloc();
#ifdef KLEE_VERIFICATION
  invariant_consume(cp);
  invariant_produce(&cp);
#else //KLEE_VERIFICATION
  while(1) {
#endif//KLEE_VERIFICATION
    int* p = recv();
    if (p == 0) continue;
    if (full(cp)) {
      int sum = pop(cp) + *p;
      send(&sum);
    } else {
      push(cp, *p);
    }
#ifdef KLEE_VERIFICATION
    invariant_consume(cp);
    invariant_produce(&cp);
#else //KLEE_VERIFICATION
  }
#endif//KLEE_VERIFICATION
}
