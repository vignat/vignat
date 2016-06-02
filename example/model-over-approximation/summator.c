/*
  The assertion will fail during verification, while
  it must not according to the contract.
  this is due to overapproximation of the model in use.
  it does not remember the latest 'pop' call, and permits
  'full' to return true after it.
  The user will see the false positive. Currently there is
  not detection built in the framework for such cases, although,
  it should be possible to automate.
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
    if (full(cp)) {
      int sum = pop(cp) + *p;
      send(&sum);
      assert(!full(cp));
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
