#include <klee/klee.h>
#include "ring.h"

bool ring_full() { return klee_int("full"); }

bool ring_empty() { return klee_int("empty"); }

void ring_push(struct packet* p) {
  klee_assert(p->port != 9); //Unnecessary.
}

void ring_pop(struct packet* p) {
  klee_make_symbolic(p, sizeof(struct packet), "popped_packet");
  klee_assume(p->port != 9);
}
