#include "vigor.h"
#include "packet.h"
#include "ring.h"

#define CAP 512

int main() {
  struct packet p;
  while(LOOP(1))
  {// Loop iteration begins.
    if (!ring_full())
      if (receive_packet(&p) && p.port != 9)
        ring_push_back(&p);
    if (!ring_empty() && can_send_packet()) {
      ring_pop_front(&p);
      ASSERT(p.port != 9);
      send_packet(&p);
    }
  }// Loop iteration ends.
  return 0;
}
