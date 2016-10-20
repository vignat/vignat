#include "vigor.h"
#include "ring.h"

struct ring {
  int dummy;
};

struct ring preallocated;

struct ring* ring_create() {
  klee_trace_ret_just_ptr(sizeof(struct ring));
  if (SYMBOLIC("alloc_success"))
    return &preallocated;
  else
    return 0;
}

bool ring_full(struct ring* r) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  return SYMBOLIC("full");
}

bool ring_empty(struct ring* r) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  return SYMBOLIC("empty");
}

void ring_push_back(struct ring* r, struct packet* p) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  klee_trace_param_ptr(p, sizeof(struct packet), "p");
  klee_trace_param_ptr_field(p, offsetof(struct packet, port),
                             sizeof(int), "port");
  ASSERT(p->port != 9); //Unnecessary.
}

void ring_pop_front(struct ring* r, struct packet* p) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  klee_trace_param_ptr(p, sizeof(struct packet), "p");
  klee_trace_param_ptr_field(p, offsetof(struct packet, port),
                             sizeof(int), "port");
  FILL_SYMBOLIC(p, sizeof(struct packet), "popped_packet");
  ASSUME(p->port != 9);
}
