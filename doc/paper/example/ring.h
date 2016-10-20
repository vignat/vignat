#ifndef _RING_H_INCLUDED_
#define _RING_H_INCLUDED_

#include "packet.h"

#define CAP 512

struct ring;

/*@
  predicate pktp(struct packet* p, int port);
  predicate ringp(struct ring* r, list<int> packets);
  @*/

struct ring* ring_create();
//@ requires true;
//@ ensures (true == ((void*)0 == (void*)result) ? true : ringp(result, nil));

bool ring_full(struct ring* r);
//@ requires ringp(r, ?lst);
//@ ensures ringp(r, lst) &*& result == (length(lst) == CAP);

bool ring_empty(struct ring* r);
//@ requires ringp(r, ?lst);
/*@ ensures ringp(r, lst) &*& result == (lst == nil); @*/

void ring_push_back(struct ring* r, struct packet* p);
//@ requires ringp(r, ?lst) &*& length(lst) < CAP &*& pktp(p, ?v);
//@ ensures ringp(r, append(lst, cons(v, nil))) &*& pktp(p, v);

void ring_pop_front(struct ring* r, struct packet* p);
//@ requires ringp(r, ?lst) &*& lst != nil &*& pktp(p, _);
//@ ensures ringp(r, tail(lst)) &*& pktp(p, head(lst));

#endif//_RING_H_INCLUDED_
