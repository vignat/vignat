
#ifndef bool
#define bool int
#define true 1
#define false 0
#endif

struct packet {
  int port;
};

bool receive_packet(struct packet* dst) {
  if (klee_int("received")) {
    dst->port = klee_int("port");
    return 1;
  }
  return 0;
}

bool can_send_packet() {
  if (klee_int("can_send_packet")) return 1;
  return 0;
}

void send_packet(struct packet* src) {
  assert(src->port != 9);
}
