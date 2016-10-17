#ifndef _PACKET_H_INCLUDED_
#define _PACKET_H_INCLUDED_

#include "vigor.h"

struct packet {
  int port;
};

static bool receive_packet(struct packet* dst) {
  if (SYMBOLIC("received")) {
    dst->port = SYMBOLIC("port");
    return 1;
  }
  return 0;
}

static bool can_send_packet() {
  if (SYMBOLIC("can_send_packet")) return 1;
  return 0;
}

static void send_packet(struct packet* src) {
  assert(src->port != 9);
}

#endif//_PACKET_H_INCLUDED_
