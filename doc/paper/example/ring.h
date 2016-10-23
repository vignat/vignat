#ifndef _RING_H_INCLUDED_
#define _RING_H_INCLUDED_

#include "packet.h"

#define CAP 512

struct ring;

/*@
  predicate ringp(struct ring* r, list<int> packets);
  @*/

struct ring* ring_create();
//@ requires true;
//@ ensures (true == ((void*)0 == (void*)result) ? true : ringp(result, nil));

bool ring_full(struct ring* r);
//@ requires ringp(r, ?lst);
/*@ ensures ringp(r, lst) &*& length(lst) <= CAP &*&
            result == (length(lst) == CAP); @*/

bool ring_empty(struct ring* r);
//@ requires ringp(r, ?lst);
/*@ ensures ringp(r, lst) &*& result == (lst == nil); @*/

void ring_push_back(struct ring* r, struct packet* p);
//@ requires ringp(r, ?lst) &*& length(lst) < CAP &*& pktp(p, ?v);
//@ ensures ringp(r, append(lst, cons(v, nil))) &*& pktp(p, v);

void ring_pop_front(struct ring* r, struct packet* p);
/*@ requires ringp(r, ?lst) &*& lst != nil &*& p->port |-> _ &*&
             struct_packet_padding(p); @*/
//@ ensures ringp(r, tail(lst)) &*& pktp(p, head(lst));

#endif//_RING_H_INCLUDED_
