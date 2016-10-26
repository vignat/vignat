#include <stdlib.h>
#include "ring.h"

//@ #include "lib/containers/modulo.gh"
//@ #include "lib/containers/stdex.gh"

struct ring {
  struct packet *array;
  int cap;
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
                  fixpoint (packet,bool) property,
                  int cap) =
    r->begin |-> ?begin &*&
    0 <= begin &*& begin < cap &*&
    r->len |-> ?len &*&
    0 <= len &*& len <= cap &*&
    len == length(packets) &*&
    r->cap |-> cap &*&
    0 < cap &*& cap < CAP_LIMIT &*&
    r->array |-> ?arr &*&
    malloc_block_chars((void*)arr, cap * sizeof(struct packet)) &*&
    malloc_block_ring(r) &*&
    begin + len < cap ?
      (empty_arrayp(arr, begin) &*&
       packetsp(arr + begin,
                len, packets,
                property) &*&
       empty_arrayp(arr + begin + len,
                    cap - len - begin)) :
      (packetsp(arr, begin + len - cap,
                drop(cap - begin, packets),
                property) &*&
       empty_arrayp(arr +
                    (begin + len - cap),
                    cap - len) &*&
       packetsp(arr + begin, cap - begin,
                take(cap - begin, packets),
                property));
  @*/

struct ring* ring_create(int capacity)
/*@ requires packet_property(?property) &*& 0 < capacity &*&
             capacity < CAP_LIMIT; @*/
//@ ensures result == 0 ? true : ringp(result, nil, property, capacity);
{
  //@ open packet_property(property);
  struct ring* ret = malloc(sizeof(struct ring));
  if (ret == 0) return 0;
  //@ packet_layout_assumption();
  /*@
    mul_bounds(sizeof (struct packet), 1024,
               capacity, CAP_LIMIT);
  @*/
  struct packet* arr = malloc(sizeof (struct packet)*capacity);
  if (arr == 0) {
    free(ret);
    return 0;
  }
  ret->array = arr;
  ret->begin = 0;
  ret->len = 0;
  ret->cap = capacity;
  //@ close empty_arrayp(ret->array, 0);
  //@ close packetsp(ret->array, 0, nil, property);
  //@ close empty_arrayp((struct packet*)ret->array, capacity);
  //@ close ringp(ret, nil, property, capacity);
  return ret;
}

bool ring_full(struct ring* r)
//@ requires ringp(r, ?lst, ?property, ?cap);
/*@ ensures ringp(r, lst, property, cap) &*&
            length(lst) <= cap &*&
            result == (length(lst) == cap); @*/
{
  //@ open ringp(r, lst, property, cap);
  return r->len == r->cap;
  //@ close ringp(r, lst, property, cap);
}

bool ring_empty(struct ring* r)
//@ requires ringp(r, ?lst, ?property, ?cap);
/*@ ensures ringp(r, lst, property, cap) &*&
            result == (lst == nil); @*/
{
  //@ open ringp(r, lst, property, cap);
  //@ switch(lst) {case cons(h,t): case nil: }
  return r->len == 0;
  //@ close ringp(r, lst, property, cap);
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
  lemma void repartition(struct packet* arr, int begin, int len, int cap)
  requires begin + len == cap &*&
           empty_arrayp(arr + begin + len, cap - len - begin) &*&
           packetsp(arr + begin, len, ?lst, ?prop) &*&
           empty_arrayp(arr, begin) &*&
           length(lst) == len;
  ensures packetsp(arr, begin + len - cap, drop(cap - begin, lst), prop) &*&
          empty_arrayp(arr + begin + len - cap, cap - len) &*&
          packetsp(arr + begin, cap - begin, take(cap - begin, lst), prop);
  {
    open empty_arrayp(arr + begin + len, cap - len - begin);
    close packetsp(arr, begin + len - cap, drop(cap - begin, lst), prop);
    mul_subst(0, (begin + len - cap), sizeof(struct packet));
  }
@*/

void ring_push_back(struct ring* r, struct packet* p)
/*@ requires ringp(r, ?lst, ?property, ?cap) &*&
             length(lst) < cap &*&
             packetp(p, ?v) &*&
             true == property(v); @*/
/*@ ensures ringp(r, append(lst, cons(v, nil)), property, cap) &*&
            packetp(p, v); @*/
{
  //@ open ringp(r, lst, property, cap);
  int end = r->begin + r->len;
  if ( r->cap <= end ) {
    end = end - r->cap;
    //@ assert r->len == length(lst);
    //@ assert 1 <= (cap - r->len);
    //@ mul_mono(1, (cap - r->len), sizeof(struct packet));
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
  //@ assert true == (0 <= cap - end - 1);
  //@ mul_mono(0, cap - end - 1, sizeof(struct packet));
  //@ chars_limits((void*)((struct packet*)r->array + end));
  //@ chars_split((void*)((struct packet*)r->array + end), sizeof(struct packet));

  //@ close_struct(tgt_pkt);
  tgt_pkt->port = p->port;
  //@ close packetp(p, v);
  //@ int old_len = r->len;
  r->len = r->len + 1;
  //@ close packetp(tgt_pkt, v);
  /*@
    if (r->begin + old_len < cap) {
      append_packet((struct packet*)r->array + r->begin);
      close empty_arrayp((struct packet*)r->array + r->begin + r->len,
                         cap - r->len - r->begin);
      if (r->begin + r->len == cap) {
        repartition(r->array, r->begin, r->len, r->cap);
      } else {
      }
    } else {
      append_packet((struct packet*)r->array);
      mul_subst(((r->begin + old_len) - cap) + 1,
                (r->begin + r->len) - cap,
                sizeof(struct packet));
      drop_append_small(cap - r->begin, lst, cons(v, nil));
      close empty_arrayp((struct packet*)r->array + r->begin + r->len - cap,
                         cap - r->len);
      take_append_small(cap - r->begin, lst, cons(v, nil));
    }
    @*/
  //@ close ringp(r, append(lst, cons(v, nil)), property, cap);
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
lemma void repartition_begin_overflow(struct packet* arr, int len, int cap)
requires packetsp(arr, len, ?lst, ?prop) &*&
         empty_arrayp(arr + len, cap - len) &*&
         packetsp(arr + cap, 0, ?empty_lst, prop) &*&
         true == ((void *)0 <= (void *)arr) &*&
         true == ((void *)arr <= (void *)UINTPTR_MAX);
ensures empty_arrayp(arr, 0) &*&
        packetsp(arr + 0, len, lst, prop) &*&
        empty_arrayp(arr + 0 + len, cap - 0 - len);
{
  packets_list_len(arr + cap);
  open packetsp(arr + cap, 0, empty_lst, prop);
  close empty_arrayp(arr, 0);
}
@*/

void ring_pop_front(struct ring* r, struct packet* p)
/*@ requires ringp(r, ?lst, ?property, ?cap) &*&
             lst != nil &*& packetp(p, _); @*/
/*@ ensures ringp(r, tail(lst), property, cap) &*&
            packetp(p, head(lst)) &*&
            true == property(head(lst)); @*/
{
  //@ open ringp(r, lst, property, cap);
  /*@ if (r->begin + r->len < cap) {
    open packetsp((struct packet*)r->array + r->begin, ?len, lst, property);
  } else {
    open packetsp((struct packet*)r->array + r->begin,
                  cap - r->begin, take(cap - r->begin, lst),
                  property);
    assert 0 < cap - r->begin;
    head_take(cap - r->begin, lst);
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
  if (r->cap <= r->begin) {
    r->begin = 0;
    //@ assert r->begin + r->len < cap;
    //@ assert cap <= old_begin + old_len;
    /*@ append_empty_place((struct packet*)r->array +
                                           old_begin + old_len - cap,
                           cap - old_len);
    @*/
    //@ mul_subst(old_begin + old_len - cap, old_len - 1, sizeof(struct packet));
    //@ repartition_begin_overflow(r->array, r->len, r->cap);
    //@ drop_n_plus_one(0, lst);
  } else {
    /*@ if (old_begin + old_len < cap) {
          append_empty_place(r->array, old_begin);
        } else {
          append_empty_place((struct packet*)r->array +
                             old_begin + old_len - cap,
                             cap - old_len);
          drop_n_plus_one(0, lst);
        }
    @*/
  }
  //@ length_tail(lst);
  //@ close packetp(p, head(lst));
  //@ close ringp(r, tail(lst), property, cap);
}
