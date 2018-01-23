#ifndef _RING_H_INCLUDED_
#define _RING_H_INCLUDED_

#include "packet.h"

#define CAP_LIMIT 1048576

struct ring;

/*@
  predicate packet_property(fixpoint (packet,bool) property) = true;
  predicate ringp(struct ring* r,
                  fixpoint (packet,bool) property,
                  list<packet> packets,
                  int capacity);
  @*/

struct ring* ring_create(int capacity);
/*@ requires packet_property(?property) &*& 0 < capacity  &*&
             capacity < CAP_LIMIT; @*/
//@ ensures result == 0 ? true : ringp(result, property, nil, capacity);

bool ring_full(struct ring* r);
//@ requires ringp(r, ?property, ?lst, ?cap);
/*@ ensures ringp(r, property, lst, cap) &*&
            length(lst) <= cap &*&
            result == (length(lst) == cap); @*/

bool ring_empty(struct ring* r);
//@ requires ringp(r, ?property, ?lst, ?cap);
/*@ ensures ringp(r, property, lst, cap) &*&
            result == (lst == nil); @*/

void ring_push_back(struct ring* r,
                    struct packet* p);
/*@ requires ringp(r, ?property, ?lst, ?cap) &*&
             length(lst) < cap &*&
             packetp(p, ?v) &*&
             true == property(v); @*/
/*@ ensures ringp(r, property, append(lst, cons(v, nil)), cap) &*&
            packetp(p, v); @*/

void ring_pop_front(struct ring* r,
                    struct packet* p);
/*@ requires ringp(r, ?property, ?lst, ?cap) &*&
             lst != nil &*& packetp(p, _); @*/
/*@ ensures ringp(r, property, tail(lst), cap) &*&
            packetp(p, head(lst)) &*&
            true == property(head(lst)); @*/

#endif//_RING_H_INCLUDED_
