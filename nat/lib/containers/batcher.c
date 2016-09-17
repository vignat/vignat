#include "batcher.h"

/*@
  predicate valsp(BATCHER_EL_TYPE* arr, int len, list<BATCHER_EL_TYPE> lst) =
    pointers(arr, len, lst);
    @*/

/*@
  predicate batcherp(list<BATCHER_EL_TYPE> batch, struct Batcher* bat) =
    bat->len |-> ?l &*&
    0 <= l &*& l <= BATCHER_CAPACITY &*&
    valsp(bat->batch, l, batch) &*&
    struct_Batcher_padding(bat) &*&
    pointers((void*)((BATCHER_EL_TYPE*)(bat->batch) + l), BATCHER_CAPACITY-l, _);

  predicate batcher_accp(struct Batcher* bat, int len) =
    bat->len |-> len &*&
    0 <= len &*& len <= BATCHER_CAPACITY &*&
    struct_Batcher_padding(bat) &*&
    pointers((void*)((BATCHER_EL_TYPE*)(bat->batch) + len),
                     BATCHER_CAPACITY-len, _);
  @*/

void batcher_init(struct Batcher* bat_out)
/*@ requires bat_out->len |-> _ &*&
             pointers(bat_out->batch, BATCHER_CAPACITY, _) &*&
             struct_Batcher_padding(bat_out); @*/
//@ ensures batcherp(nil, bat_out);
{
  bat_out->len = 0;
  //@ close valsp(bat_out->batch, 0, nil);
  //@ close batcherp(nil, bat_out);
}

void batcher_push(struct Batcher *bat, BATCHER_EL_TYPE val)
//@ requires batcherp(?b, bat) &*& length(b) < BATCHER_CAPACITY;
//@ ensures batcherp(append(b, cons(val, nil)), bat);
{
  //@ open batcherp(b, bat);
  //@ open valsp(bat->batch, bat->len, b);
  bat->batch[bat->len] = val;
  ++bat->len;
  //@ close pointers((void*)((BATCHER_EL_TYPE*)(bat->batch) + bat->len-1), 1, cons(val, nil));
  //@ pointers_join(bat->batch);
  //@ close valsp(bat->batch, bat->len, append(b, cons(val, nil)));
  //@ close batcherp(append(b, cons(val, nil)), bat);
}

void batcher_take_all(struct Batcher *bat,
                      BATCHER_EL_TYPE **vals_out, int *count_out)
//@ requires batcherp(?b, bat) &*& pointer(vals_out, _) &*& *count_out |-> _;
/*@ ensures batcher_accp(bat, length(b)) &*& *vals_out |-> ?vals &*&
            vals == batcher_contents(bat) &*&
            *count_out |-> length(b) &*& valsp(vals, length(b), b) &*&
            length(b) <= BATCHER_CAPACITY; @*/
{
  //@ open batcherp(b, bat);
  //@ open valsp(bat->batch, bat->len, b);
  *vals_out = bat->batch;
  *count_out = bat->len;
  //@ close valsp(bat->batch, bat->len, b);
  //@ close batcher_accp(bat, length(b));
}

void batcher_empty(struct Batcher *bat)
/*@ requires batcher_accp(bat, ?len) &*&
             valsp(batcher_contents(bat), len, _); @*/
//@ ensures batcherp(nil, bat);
{
  //@ open batcher_accp(bat, len);
  bat->len = 0;
  //@ open valsp(batcher_contents(bat), len, _);
  //@ close valsp(bat->batch, 0, nil);
  //@ close batcherp(nil, bat);
}

int batcher_full(struct Batcher *bat)
//@ requires batcherp(?b, bat);
/*@ ensures batcherp(b, bat) &*&
            (length(b) == BATCHER_CAPACITY ?
             result == 1 :
             result == 0); @*/
{
  //@ open batcherp(b, bat);
  //@ open valsp(bat->batch, bat->len, b);
  return (BATCHER_CAPACITY <= bat->len) ? 1 : 0;
  //@ close valsp(bat->batch, bat->len, b);
  //@ close batcherp(b, bat);
}

int batcher_is_empty(struct Batcher *bat)
//@ requires batcherp(?b, bat);
//@ ensures batcherp(b, bat) &*& (b == nil ? result == 1 : result == 0);
{
  //@ open batcherp(b, bat);
  //@ open valsp(bat->batch, bat->len, b);
  /*@ switch(b) {
      case nil: assert(bat->len == 0);
      case cons(h,t): assert(0 < bat->len);
    }
    @*/
  return (bat->len <= 0) ? 1 : 0;
  //@ close valsp(bat->batch, bat->len, b);
  //@ close batcherp(b, bat);
}
