#ifndef _RING_H_INCLUDED_
#define _RING_H_INCLUDED_

#include "packet.h"

#define CAP 512

struct ring;

/*@
  predicate packet_property(fixpoint (packet,bool) property) = true;
  predicate ringp(struct ring* r, list<packet> packets,
                  fixpoint (packet,bool) property);
  @*/

struct ring* ring_create();
//@ requires packet_property(?property);
//@ ensures result == 0 ? true : ringp(result, nil, property);

bool ring_full(struct ring* r);
//@ requires ringp(r, ?lst, ?property);
/*@ ensures ringp(r, lst, property) &*&
            length(lst) <= CAP &*&
            result == (length(lst) == CAP); @*/

bool ring_empty(struct ring* r);
//@ requires ringp(r, ?lst, ?property);
/*@ ensures ringp(r, lst, property) &*&
            result == (lst == nil); @*/

void ring_push_back(struct ring* r,
                    struct packet* p);
/*@ requires ringp(r, ?lst, ?property) &*&
             length(lst) < CAP &*&
             packetp(p, ?v) &*&
             true == property(v); @*/
/*@ ensures ringp(r, append(lst, cons(v, nil)), property) &*&
            packetp(p, v); @*/

void ring_pop_front(struct ring* r,
                    struct packet* p);
/*@ requires ringp(r, ?lst, ?property) &*&
             lst != nil &*& packetp(p, _); @*/
/*@ ensures ringp(r, tail(lst), property) &*&
            packetp(p, head(lst)) &*&
            true == property(head(lst)); @*/

#endif//_RING_H_INCLUDED_
