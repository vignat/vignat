#include "vigor.h"
#include "packet.h"

#define CAP 512

int main() {
  struct packet packets[CAP] = {};
  int begin = 0, end = 0;

  while(1) {
    if (end != (begin - 1) || !(end == CAP - 1 && begin == 0)) {
      if (receive_packet(&packets[end]) && packets[end].port != 9)
        end = (end + 1)%CAP;
    }
    if (end != begin && can_send_packet()) {
      ASSERT(packets[begin].port != 9);
      send_packet(&packets[begin]);
      begin = (begin + 1)%CAP;
    }
  }
  return 0;
}
