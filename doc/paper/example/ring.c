#include "ring.h"

//@ #include "lib/containers/modulo.gh"

struct ring {
  struct packet array[CAP];
  int begin;
  int len;
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
    r->len |-> ?len &*&
    0 <= len &*& len <= CAP &*&
    len == length(packets) &*&
    begin + len < CAP ?
      (empty_arrayp(r->array, begin) &*&
       packetsp((struct packet*)r->array + begin, len, packets) &*&
       empty_arrayp((struct packet*)r->array + begin + len, CAP - len - begin)) :
      (packetsp((struct packet*)r->array, begin + len - CAP,
                drop(CAP - begin, packets)) &*&
       empty_arrayp((struct packet*)r->array + (begin + len - CAP),
                    CAP - len) &*&
       packetsp((struct packet*)r->array + begin, CAP - begin,
                take(CAP - begin, packets)));
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
  return r->len == CAP;
  //@ close ringp(r, lst);
}

bool ring_empty(struct ring* r)
//@ requires ringp(r, ?lst);
/*@ ensures ringp(r, lst) &*& result == (lst == nil); @*/
{
  //@ open ringp(r, lst);
  //@ switch(lst) {case cons(h,t): case nil: }
  return r->len == 0;
  //@ close ringp(r, lst);
}

/*@
lemma void div_less(int a, int b)
requires 0 <= a &*& a < b;
ensures 0 == a/b;
{
  assume(0 == a/b);
}
@*/

void ring_push_back(struct ring* r, struct packet* p)
//@ requires ringp(r, ?lst) &*& length(lst) < CAP &*& pktp(p, ?v);
//@ ensures ringp(r, append(lst, cons(v, nil))) &*& pktp(p, v);
{
  //@ open ringp(r, lst);
  int end = (r->begin + r->len) % CAP;
  //@ div_mod_gt_0(end, r->begin + r->len, CAP);
  /*@
  if (r->begin + r->len < CAP) {
    div_rem(r->begin + r->len, CAP);
    div_less(r->begin + r->len, CAP);
    assert(0 == (r->begin + r->len)/CAP);
    assert(end == r->begin + r->len);
    open empty_arrayp(r->array + end, CAP - r->len - r->begin);
  } else {
    //assert(end == r->begin + r->len - CAP);
    
  }
  @*/
  struct packet* tgt_pkt = (struct packet*)r->array + end;
  tgt_pkt->port = p->port;
  //@ close pktp(p, v);
  r->len = r->len + 1;
  //@ close ringp(r, append(lst, cons(v, nil)));
}

void ring_pop_front(struct ring* r, struct packet* p)
//@ requires ringp(r, ?lst) &*& lst != nil &*& pktp(p, _);
//@ ensures ringp(r, tail(lst)) &*& pktp(p, head(lst));
{
  //@ open ringp(r, lst);
  *p = r->array[r->begin];
  r->len = r->len - 1;
  r->begin = r->begin + 1;
  if (CAP <= r->begin) r->begin = 0;
  //@ close ringp(r, tail(lst));
}
