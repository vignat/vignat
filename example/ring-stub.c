#include "vigor.h"
#include "ring.h"
#include "user-params.h"

struct ring {
  int dummy;
};

bool last_full = false;

struct ring preallocated;

struct ring* ring_create(int capacity) {
  klee_trace_ret_just_ptr(sizeof(struct ring));
  klee_trace_param_i32(capacity, "capacity");
  if (SYMBOLIC("alloc_success"))
    return &preallocated;
  else
    return 0;
}

bool ring_full(struct ring* r) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  last_full = SYMBOLIC("full");
  if (last_full) {
    return true;
  } else {
    return false;
  }
}

bool ring_empty(struct ring* r) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  if (!last_full && SYMBOLIC("empty")) {
    return true;
  } else {
    return false;
  }
}

void ring_push_back(struct ring* r, struct packet* p) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  klee_trace_param_ptr(p, sizeof(struct packet), "p");
  klee_trace_param_ptr_field(p, offsetof(struct packet, port),
                             sizeof(int), "port");
  ASSERT(packet_constraints(p)); //Unnecessary.
}

void ring_pop_front(struct ring* r, struct packet* p) {
  klee_trace_ret();
  klee_trace_param_just_ptr(r, sizeof(struct ring), "r");
  klee_trace_param_ptr(p, sizeof(struct packet), "p");
  klee_trace_param_ptr_field(p, offsetof(struct packet, port),
                             sizeof(int), "port");
  FILL_SYMBOLIC(p, sizeof(struct packet), "popped_packet");
  ASSUME(packet_constraints(p));
}
