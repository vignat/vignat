/*
  This example demonstrates a common mistake.
  After 'recv' function called its result is implied
  to be a valid pointer which it may be not.
  Thanks to a detailed enought symbolic model,
  the verifier will detect and report the possible
  wrong memory access.
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
    if (full(cp)) {
      int sum = pop(cp) + *p;
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
