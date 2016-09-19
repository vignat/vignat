#include "vigor.h"
#include "ring.h"

bool ring_full() { return SYMBOLIC("full"); }

bool ring_empty() { return SYMBOLIC("empty"); }

void ring_push_back(struct packet* p) {
  ASSERT(p->port != 9); //Unnecessary.
}

void ring_pop_front(struct packet* p) {
  FILL_SYMBOLIC(p, sizeof(struct packet), "popped_packet");
  ASSUME(p->port != 9);
}
