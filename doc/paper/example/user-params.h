#ifndef _USER_PARAMS_H_INCLUDED_
#define _USER_PARAMS_H_INCLUDED_

#include "packet.h"
#include "ring.h"

/*@
  fixpoint bool port_non9(packet p) {
    switch(p) { case packet(port): return port != 9; }
  }
  @*/

/*@
  predicate loop_invariant(struct ring* rp) = ringp(rp, _, port_non9);
  @*/

static bool packet_constraints(struct packet* p) {
  return p->port != 9;
}

#endif//_USER_PARAMS_H_INCLUDED_
