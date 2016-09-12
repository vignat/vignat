#include <klee/klee.h>
#include "packet.h"

#define CAP 64

int main() {
  struct packet packets[CAP] = {};
  int begin = 0, end = 0;

  for (int i = 0; i < (end + CAP - begin)%CAP; ++i)
    klee_assert(packets[(i+begin)%CAP].port != 9);

  klee_make_symbolic(packets, sizeof(packets), "packets");
  begin = klee_range(0, CAP, "begin");
  end = klee_range(0, CAP, "end");

  for (int i = 0; i < (end + CAP - begin)%CAP; ++i)
    klee_assume(packets[(i+begin)%CAP].port != 9);// Note the semicolon

  {// Loop iteration begins.
    if (end != (begin - 1) || !(end == CAP - 1 && begin == 0)) {
      if (receive_packet(&packets[end] && packets[end].port != 9)
        end = (end + 1)%CAP;
    }
    if (end != begin && can_send_packet()) {
      assert(packets[begin].port != 9);
      send_packet(&packets[begin]);
      begin = (begin + 1)%CAP;
    }
  }//Loop iteration ends

  for (int i = 0; i < (end + CAP - begin)%CAP; ++i)
    klee_assert(packets[(i+begin)%CAP].port != 9);
  return 0;
}
