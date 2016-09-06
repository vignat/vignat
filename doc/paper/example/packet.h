#ifndef _PACKET_H_INCLUDED_
#define _PACKET_H_INCLUDED_
#ifndef bool
#define bool int
#define true 1
#define false 0
#endif

struct packet {
  int port;
};

inline bool receive_packet(struct packet* dst) {
  if (klee_int("received")) {
    dst->port = klee_int("port");
    return 1;
  }
  return 0;
}

inline bool can_send_packet() {
  if (klee_int("can_send_packet")) return 1;
  return 0;
}

inline void send_packet(struct packet* src) {
  assert(src->port != 9);
}

#endif//_PACKET_H_INCLUDED_
