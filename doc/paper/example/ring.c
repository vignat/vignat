#include "ring.h"

struct ring {
  struct packet array[CAP];
  int begin;
  int end;
};


/*@
  predicate pktp(struct packet* p, int port) =
    p->port |-> port &*& port != 9;

  predicate empty_arrayp(struct packet* arr, int len) =
    chars((void*)arr, len*sizeof(struct packet), _);

  predicate packetsp(struct packet* arr, int len, list<int> pkts) =
    switch(pkts) {
      case nil: return len == 0;
      case cons(h,t):
        return pktp(arr, h) &*& packetsp(arr+1, len-1, t);
    };

  predicate ringp(struct ring* r, list<int> packets) =
    r->begin |-> ?begin &*&
    0 <= begin &*& begin < CAP &*&
    r->end |-> ?end &*&
    0 <= end &*& end < CAP &*&
    begin < end ?
      (end - begin == length(packets) &*&
       empty_arrayp(r->array, begin) &*&
       packetsp((struct packet*)r->array + begin, end - begin, packets) &*&
       empty_arrayp((struct packet*)r->array + end, CAP - end)) :
      (CAP - begin + end == length(packets) &*&
       packetsp((struct packet*)r->array, end, take(end, packets)) &*&
       empty_arrayp((struct packet*)r->array + end, begin - end) &*&
       packetsp((struct packet*)r->array + begin, CAP - begin, drop(end, packets)));
  @*/

struct ring* ring_create()
//@ requires true;
//@ ensures result == 0 ? true : ringp(result, nil);
{
  return 0;
}

bool ring_full(struct ring* r)
//@ requires ringp(r, ?lst);
//@ ensures ringp(r, lst) &*& result == (length(lst) == CAP);
{
  //@ open ringp(r, lst);
  if (r->begin == 0) {
    return r->end == CAP-1;
    //@ close ringp(r, lst);
  }
  return r->begin == end-1;
  //@ close ringp(r, lst);
}

bool ring_empty(struct ring* r)
//@ requires ringp(r, ?lst);
/*@ ensures ringp(r, lst) &*& result == (lst == nil); @*/
{
  return r->begin == r->end;
}

void ring_push_back(struct ring* r, struct packet* p)
//@ requires ringp(r, ?lst) &*& length(lst) < CAP &*& pktp(p, ?v);
//@ ensures ringp(r, append(lst, cons(v, nil))) &*& pktp(p, v);
{
  r->array[r->end] = *p;
  r->end = r->end + 1;
  if (CAP <= r->end) r->end = 0;
}

void ring_pop_front(struct ring* r, struct packet* p)
//@ requires ringp(r, ?lst) &*& lst != nil &*& pktp(p, _);
//@ ensures ringp(r, tail(lst)) &*& pktp(p, head(lst));
{
  *p = r->array[r->begin];
  r->begin = r->begin + 1;
  if (CAP <= r->begin) r->begin = 0;
}
