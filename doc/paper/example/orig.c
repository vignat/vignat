#include "vigor.h"
#include "packet.h"

#define CAP 512

int main() {
  struct packet packets[CAP] = {};
  int begin = 0, queue_len = 0;

  while(1) {
    if (queue_len < CAP) {
      int end = (begin + queue_len)%CAP;
      if (receive_packet(&packets[end]) &&
          packets[end].port != 9)
        queue_len += 1;
    }
    if (0 < queue_len && can_send_packet()) {
      send_packet(&packets[begin]);
      begin = (begin + 1)%CAP;
    }
  }
  return 0;
}
