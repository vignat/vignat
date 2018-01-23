#include "vigor.h"
#include "packet.h"
#include "ring.h"
#include "loop-model.h"
#include "user-params.h"

int main(int argc, char** argv) {
  struct packet p;
  struct ring *r = ring_create(RING_CAPACITY);
  if (!r) return 1;
  while(LOOP(1))
  {
    loop_iteration_begin(&r);
    if (!ring_full(r))
      if (receive_packet(&p) && p.port != 9)
        ring_push_back(r, &p);
    if (!ring_empty(r) && can_send_packet()) {
      ring_pop_front(r, &p);
      VIGOR_CHECK(p.port != 9);
      send_packet(&p);
    }
    loop_iteration_end(&r);
  }
  return 0;
}
