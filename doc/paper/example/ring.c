#include "ring.h"

//@ #include "lib/containers/modulo.gh"
//@ #include "lib/containers/stdex.gh"

struct ring {
  struct packet array[CAP];
  int begin;
  int len;
};


/*@
  predicate pktp(struct packet* p, int port) =
    struct_packet_padding(p) &*&
    p->port |-> port &*& port != 9;

  predicate empty_arrayp(struct packet* arr, int len) =
    true == ((char *)0 <= (void *)(arr)) &*&
    true == ((void *)(arr) <= (char *)UINTPTR_MAX) &*&
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
  lemma void append_packet(struct packet* arr)
  requires packetsp(arr, ?len, ?lst) &*& len == length(lst) &*& pktp(arr+len, ?v);
  ensures packetsp(arr, len+1, append(lst, cons(v, nil)));
  {
    open packetsp(arr, len, lst);
    switch (lst) {
      case nil:
        assert len == 0;
        close packetsp(arr+1, 0, nil);
        close packetsp(arr, 1, cons(v, nil));
      case cons(h, t):
        append_packet(arr + 1);
        close packetsp(arr, len+1, append(lst, cons(v, nil)));
    }
  }
  @*/
  
/*@
  lemma void repartition(struct packet* arr, int begin, int len)
  requires begin + len == CAP &*&
           empty_arrayp(arr + begin + len, CAP - len - begin) &*&
           packetsp(arr + begin, len, ?lst) &*&
           empty_arrayp(arr, begin) &*&
           length(lst) == len;
  ensures packetsp(arr, begin + len - CAP, drop(CAP - begin, lst)) &*&
          empty_arrayp(arr + begin + len - CAP, CAP - len) &*&
          packetsp(arr + begin, CAP - begin, take(CAP - begin, lst));
  {
    open empty_arrayp(arr + begin + len, CAP - len - begin);
    close packetsp(arr, begin + len - CAP, drop(CAP - begin, lst));
    mul_subst(0, (begin + len - CAP), sizeof(struct packet));
  }
@*/

void ring_push_back(struct ring* r, struct packet* p)
//@ requires ringp(r, ?lst) &*& length(lst) < CAP &*& pktp(p, ?v);
//@ ensures ringp(r, append(lst, cons(v, nil))) &*& pktp(p, v);
{
  //@ open ringp(r, lst);
  int end = r->begin + r->len;
  if ( CAP <= end ) {
    end = end - CAP;
    //@ assert r->len == length(lst);
    //@ assert 1 <= (CAP - r->len);
    //@ mul_mono(1, (CAP - r->len), sizeof(struct packet));
  } else {
    //@ assert end == r->begin + r->len;
    //@ mul_subst(end, r->begin + r->len, sizeof(struct packet));
    //@ assert true == ((struct packet*)r->array + end == (struct packet*)r->array + r->begin + r->len);
  }
  /*@
  open empty_arrayp((struct packet*)r->array + end,
                    _);
  @*/
  
  // @ chars_limits((void*)((struct packet*)r->array + r->begin + r->len));
  struct packet* tgt_pkt = (struct packet*)r->array + end;
  //@ open pktp(p, v);
  //@ assert true == (0 <= CAP - end - 1);
  //@ mul_mono(0, CAP - end - 1, sizeof(struct packet));
  //@ chars_limits((void*)((struct packet*)r->array + end));
  //@ chars_split((void*)((struct packet*)r->array + end), sizeof(struct packet));
  
  //@ close_struct(tgt_pkt);
  tgt_pkt->port = p->port;
  //@ close pktp(p, v);
  //@ int old_len = r->len;
  r->len = r->len + 1;
  //@ close pktp(tgt_pkt, v);
  /*@
    if (r->begin + old_len < CAP) {
      append_packet((struct packet*)r->array + r->begin);
      close empty_arrayp((struct packet*)r->array + r->begin + r->len,
                         CAP - r->len - r->begin);
      if (r->begin + r->len == CAP) {
        repartition(r->array, r->begin, r->len);
      } else {
      }
    } else {
      append_packet((struct packet*)r->array);
      assert true == (((r->begin + old_len) - CAP) + 1 == (r->begin + r->len) - CAP);
      mul_subst(((r->begin + old_len) - CAP) + 1, (r->begin + r->len) - CAP, sizeof(struct packet));
      drop_append_small(CAP - r->begin, lst, cons(v, nil));
      assert append(drop(CAP - r->begin, lst), cons(v, nil)) == drop(CAP - r->begin, append(lst, cons(v, nil)));
      close empty_arrayp((struct packet*)r->array + r->begin + r->len - CAP,
                         CAP - r->len);
      take_append_small(CAP - r->begin, lst, cons(v, nil));
    }
    @*/
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
