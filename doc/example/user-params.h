#ifndef _USER_PARAMS_H_INCLUDED_
#define _USER_PARAMS_H_INCLUDED_

#include "packet.h"
#include "ring.h"

#define RING_CAPACITY 512

/*@
  fixpoint bool packet_constraints_fp(packet p) {
    switch(p) { case packet(port): return port != 9; }
  }
  @*/

static bool packet_constraints(struct packet* p) {
  return p->port != 9;
}

#endif//_USER_PARAMS_H_INCLUDED_
