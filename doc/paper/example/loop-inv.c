#include "vigor.h"
#include "packet.h"

#define CAP 64

int main() {
  struct packet packets[CAP] = {};
  int begin = 0, end = 0;

  FOR_EVERY_RING_ELEMENT(i, begin, end, ASSERT(packets[i].port != 9));

  FILL_SYMBOLIC(packets, sizeof(packets), "packets");
  begin = SYMBOLIC_RANGE(0, CAP, "begin");
  end = SYMBOLIC_RANGE(0, CAP, "end");

  while(LOOP(1))
  {// Loop iteration begins.
    ASSUME(0 <= begin & begin < CAP &
           0 <= end & end < CAP);
    FOR_EVERY_RING_ELEMENT(i, begin, end, ASSUME(packets[i].port != 9));

    if (end != (begin - 1) || !(end == CAP - 1 && begin == 0)) {
      if (receive_packet(&packets[end]) && packets[end].port != 9)
        end = (end + 1)%CAP;
    }
    if (end != begin && can_send_packet()) {
      ASSERT(packets[begin].port != 9);
      send_packet(&packets[begin]);
      begin = (begin + 1)%CAP;
    }
    ASSERT(0 <= begin & begin < CAP &
           0 <= end & end < CAP);
    FOR_EVERY_RING_ELEMENT(i, begin, end, ASSERT(packets[i].port != 9));
  }//Loop iteration ends

  return 0;
}
