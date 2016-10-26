#include "ring.h"

//@ #include "lib/containers/modulo.gh"
//@ #include "lib/containers/stdex.gh"

struct ring {
  struct packet array[CAP];
  int begin;
  int len;
};


/*@
  predicate empty_arrayp(struct packet* arr, int len) =
    true == ((char *)0 <= (void *)(arr)) &*&
    true == ((void *)(arr) <= (char *)UINTPTR_MAX) &*&
    chars((void*)arr, len*sizeof(struct packet), _);

  predicate packetsp(struct packet* arr, int len,
                     list<packet> pkts,
                     fixpoint (packet,bool) property) =
    switch(pkts) {
      case nil: return len == 0;
      case cons(h,t):
        return true == ((void*)arr <= (void*)UINTPTR_MAX) &*&
               true == ((void*)0 <= (void*)(arr)) &*&
               packetp(arr, h) &*&
               true == property(h) &*&
               packetsp(arr+1, len-1, t, property);
    };

  predicate ringp(struct ring* r,
                  list<packet> packets,
                  fixpoint (packet,bool) property) =
    r->begin |-> ?begin &*&
    0 <= begin &*& begin < CAP &*&
    r->len |-> ?len &*&
    0 <= len &*& len <= CAP &*&
    len == length(packets) &*&
    malloc_block_ring(r) &*&
    begin + len < CAP ?
      (empty_arrayp(r->array, begin) &*&
       packetsp((struct packet*)r->array + begin,
                len, packets,
                property) &*&
       empty_arrayp((struct packet*)r->array + begin + len,
                    CAP - len - begin)) :
      (packetsp((struct packet*)r->array, begin + len - CAP,
                drop(CAP - begin, packets),
                property) &*&
       empty_arrayp((struct packet*)r->array +
                    (begin + len - CAP),
                    CAP - len) &*&
       packetsp((struct packet*)r->array + begin, CAP - begin,
                take(CAP - begin, packets),
                property));
  @*/

struct ring* ring_create()
//@ requires packet_property(?property);
//@ ensures result == 0 ? true : ringp(result, nil, property);
{
  //@ open packet_property(property);
  struct ring* ret = malloc(sizeof(struct ring));
  if (ret == 0) return 0;
  ret->begin = 0;
  ret->len = 0;
  //@ close empty_arrayp(ret->array, 0);
  //@ close packetsp(ret->array, 0, nil, property);
  //@ close empty_arrayp((struct packet*)ret->array, CAP);
  //@ close ringp(ret, nil, property);
  return ret;
}

bool ring_full(struct ring* r)
//@ requires ringp(r, ?lst, ?property);
/*@ ensures ringp(r, lst, property) &*&
            length(lst) <= CAP &*&
            result == (length(lst) == CAP); @*/
{
  //@ open ringp(r, lst, property);
  return r->len == CAP;
  //@ close ringp(r, lst, property);
}

bool ring_empty(struct ring* r)
//@ requires ringp(r, ?lst, ?property);
/*@ ensures ringp(r, lst, property) &*&
            result == (lst == nil); @*/
{
  //@ open ringp(r, lst, property);
  //@ switch(lst) {case cons(h,t): case nil: }
  return r->len == 0;
  //@ close ringp(r, lst, property);
}

/*@
  lemma void append_packet(struct packet* arr)
  requires packetsp(arr, ?len, ?lst, ?prop) &*& len == length(lst) &*&
           packetp(arr+len, ?v) &*&
           true == prop(v) &*&
           true == ((void*)(arr + len) < (void*)UINTPTR_MAX) &*&
           true == ((void*)0 <= (void*)(arr + len));
  ensures packetsp(arr, len+1, append(lst, cons(v, nil)), prop);
  {
    close save_for_now((void*)(arr + len) < (void*)UINTPTR_MAX);
    close save_for_now((void*)0 <= (void*)(arr + len));
    open packetsp(arr, len, lst, prop);
    switch (lst) {
      case nil:
        assert len == 0;
        open save_for_now((void*)(arr + len) < (void*)UINTPTR_MAX);
        open save_for_now((void*)0 <= (void*)(arr + len));
        close packetsp(arr+1, 0, nil, prop);
        close packetsp(arr, 1, cons(v, nil), prop);
      case cons(h, t):
        open save_for_now(_);
        open save_for_now(_);
        append_packet(arr + 1);
        close packetsp(arr, len+1, append(lst, cons(v, nil)), prop);
    }
  }
  @*/
  
/*@
  lemma void repartition(struct packet* arr, int begin, int len)
  requires begin + len == CAP &*&
           empty_arrayp(arr + begin + len, CAP - len - begin) &*&
           packetsp(arr + begin, len, ?lst, ?prop) &*&
           empty_arrayp(arr, begin) &*&
           length(lst) == len;
  ensures packetsp(arr, begin + len - CAP, drop(CAP - begin, lst), prop) &*&
          empty_arrayp(arr + begin + len - CAP, CAP - len) &*&
          packetsp(arr + begin, CAP - begin, take(CAP - begin, lst), prop);
  {
    open empty_arrayp(arr + begin + len, CAP - len - begin);
    close packetsp(arr, begin + len - CAP, drop(CAP - begin, lst), prop);
    mul_subst(0, (begin + len - CAP), sizeof(struct packet));
  }
@*/

void ring_push_back(struct ring* r, struct packet* p)
/*@ requires ringp(r, ?lst, ?property) &*&
             length(lst) < CAP &*&
             packetp(p, ?v) &*&
             true == property(v); @*/
/*@ ensures ringp(r, append(lst, cons(v, nil)), property) &*&
            packetp(p, v); @*/
{
  //@ open ringp(r, lst, property);
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
    open empty_arrayp((struct packet*)r->array + end, _);
  @*/
  struct packet* tgt_pkt = (struct packet*)r->array + end;
  //@ open packetp(p, v);
  //@ assert true == (0 <= CAP - end - 1);
  //@ mul_mono(0, CAP - end - 1, sizeof(struct packet));
  //@ chars_limits((void*)((struct packet*)r->array + end));
  //@ chars_split((void*)((struct packet*)r->array + end), sizeof(struct packet));

  //@ close_struct(tgt_pkt);
  tgt_pkt->port = p->port;
  //@ close packetp(p, v);
  //@ int old_len = r->len;
  r->len = r->len + 1;
  //@ close packetp(tgt_pkt, v);
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
  //@ close ringp(r, append(lst, cons(v, nil)), property);
}

/*@
  lemma void append_empty_place(struct packet* arr, int begin)
  requires empty_arrayp(arr, begin) &*&
           chars((void*)(arr + begin), sizeof(struct packet), _);
  ensures empty_arrayp(arr, begin+1);
  {
    open empty_arrayp(arr, begin);
    chars_join((void*)arr);
    close empty_arrayp(arr, begin+1);
  }
@*/

/*@
lemma void packets_list_len(struct packet* arr)
requires packetsp(arr, ?len, ?lst, ?property);
ensures packetsp(arr, len, lst, property) &*& len == length(lst);
{
  open packetsp(arr, len, lst, property);
  switch(lst) {
    case nil: break;
    case cons(h, t):
      packets_list_len(arr+1);
      break;
  }
  close packetsp(arr, len, lst, property);
}
@*/

/*@
lemma void repartition_begin_overflow(struct packet* arr, int len)
requires packetsp(arr, len, ?lst, ?prop) &*&
         empty_arrayp(arr + len, CAP - len) &*&
         packetsp(arr + CAP, 0, ?empty_lst, prop) &*&
         true == ((void *)0 <= (void *)arr) &*&
         true == ((void *)arr <= (void *)UINTPTR_MAX);
ensures empty_arrayp(arr, 0) &*&
        packetsp(arr + 0, len, lst, prop) &*&
        empty_arrayp(arr + 0 + len, CAP - 0 - len);
{
  packets_list_len(arr + CAP);
  open packetsp(arr + CAP, 0, empty_lst, prop);
  close empty_arrayp(arr, 0);
}
@*/

void ring_pop_front(struct ring* r, struct packet* p)
/*@ requires ringp(r, ?lst, ?property) &*&
             lst != nil &*& packetp(p, _); @*/
/*@ ensures ringp(r, tail(lst), property) &*&
            packetp(p, head(lst)) &*&
            true == property(head(lst)); @*/
{
  //@ open ringp(r, lst, property);
  /*@ if (r->begin + r->len < CAP) {
    open packetsp((struct packet*)r->array + r->begin, ?len, lst, property);
  } else {
    open packetsp((struct packet*)r->array + r->begin,
                  CAP - r->begin, take(CAP - r->begin, lst),
                  property);
    assert 0 < CAP - r->begin;
    head_take(CAP - r->begin, lst);
  }
  @*/
  struct packet* src_pkt = (struct packet*)r->array + r->begin;
  //@ open packetp(src_pkt, head(lst));
  //@ open packetp(p, _);
  p->port = src_pkt->port;
  //@ open_struct(src_pkt);
  //@ int old_len = r->len;
  //@ int old_begin = r->begin;
  r->len = r->len - 1;
  r->begin = r->begin + 1;
  if (CAP <= r->begin) {
    r->begin = 0;
    //@ assert r->begin + r->len < CAP;
    //@ assert CAP <= old_begin + old_len;
    /*@ append_empty_place((struct packet*)r->array +
                                           old_begin + old_len - CAP,
                           CAP - old_len);
      @*/
    //@ repartition_begin_overflow(r->array, r->len);
    //@ drop_n_plus_one(0, lst);
  } else {
    /*@ if (old_begin + old_len < CAP) {
          append_empty_place(r->array, old_begin);
        } else {
          append_empty_place((struct packet*)r->array + old_begin + old_len - CAP, CAP - old_len);
          drop_n_plus_one(0, lst);
        }
    @*/
  }
  //@ length_tail(lst);
  //@ close packetp(p, head(lst));
  //@ close ringp(r, tail(lst), property);
}
