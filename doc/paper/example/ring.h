#ifndef _RING_H_INCLUDED_
#define _RING_H_INCLUDED_

#include "packet.h"

#define CAP_LIMIT 1048576

struct ring;

/*@
  predicate packet_property(fixpoint (packet,bool) property) = true;
  predicate ringp(struct ring* r, list<packet> packets,
                  fixpoint (packet,bool) property,
                  int capacity);
  @*/

struct ring* ring_create(int capacity);
/*@ requires packet_property(?property) &*& 0 < capacity  &*&
             capacity < CAP_LIMIT; @*/
//@ ensures result == 0 ? true : ringp(result, nil, property, capacity);

bool ring_full(struct ring* r);
//@ requires ringp(r, ?lst, ?property, ?cap);
/*@ ensures ringp(r, lst, property, cap) &*&
            length(lst) <= cap &*&
            result == (length(lst) == cap); @*/

bool ring_empty(struct ring* r);
//@ requires ringp(r, ?lst, ?property, ?cap);
/*@ ensures ringp(r, lst, property, cap) &*&
            result == (lst == nil); @*/

void ring_push_back(struct ring* r,
                    struct packet* p);
/*@ requires ringp(r, ?lst, ?property, ?cap) &*&
             length(lst) < cap &*&
             packetp(p, ?v) &*&
             true == property(v); @*/
/*@ ensures ringp(r, append(lst, cons(v, nil)), property, cap) &*&
            packetp(p, v); @*/

void ring_pop_front(struct ring* r,
                    struct packet* p);
/*@ requires ringp(r, ?lst, ?property, ?cap) &*&
             lst != nil &*& packetp(p, _); @*/
/*@ ensures ringp(r, tail(lst), property, cap) &*&
            packetp(p, head(lst)) &*&
            true == property(head(lst)); @*/

#endif//_RING_H_INCLUDED_
