#include <klee/klee.h>
#include "packet.h"

#define CAP 512

bool ring_full() { return klee_int("full"); }

bool ring_empty() { return klee_int("empty"); }

void ring_push(struct packet* p) {
  klee_assert(p->port != 9); //Unnecessary.
}

void ring_pop(struct packet* p) {
  klee_make_symbolic(p, sizeof(struct packet), "popped_packet");
  klee_assume(p->port != 9);
}

int main() {
  {
    struct packet p;
    if (!ring_full())
      if (receive_packet(&p) && p.port != 9)
        ring_push(&p);
    if (!ring_empty() && can_send_packet()) {
      ring_pop(&p);
      assert(p.port != 9);
      send_packet(&p);
    }
  }
  return 0;
}
