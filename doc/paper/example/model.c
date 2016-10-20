#include "vigor.h"
#include "packet.h"
#include "ring.h"

int main(int argc, char** argv) {
  struct packet p;
  struct ring *r = ring_create();
  //mistake: no check for null here!
  while(LOOP(1))
  {// Loop iteration begins.
    if (!ring_full(r))
      if (receive_packet(&p) && p.port != 9)
        ring_push_back(r, &p);
    if (!ring_empty(r) && can_send_packet()) {
      ring_pop_front(r, &p);
      ASSERT(p.port != 9);
      send_packet(&p);
    }
  }// Loop iteration ends.
  return 0;
}
