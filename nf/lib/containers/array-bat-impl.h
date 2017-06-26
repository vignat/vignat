#ifndef _ARRAY_BAT_IMPL_H_INCLUDED_
#define _ARRAY_BAT_IMPL_H_INCLUDED_
#include "array-bat.h"
#include "../ignore.h"

//@ #include "arith.gh"
//@ #include "stdex.gh"

/*@
  predicate batcherpp(list<BATCHER_EL_TYPE> batch, struct Batcher* bat) =
    batcherp(batch, bat) &*& length(batch) < BATCHER_CAPACITY;
  predicate bat_arrp(struct Batcher *bp, int len,
                     list<list<BATCHER_EL_TYPE> > bats) =
    switch(bats) {
      case nil: return len == 0;
      case cons(h,t):
        return batcherpp(h, bp) &*&
               bat_arrp(bp+1, len-1, t);
    };


  predicate arrp_bat(list<list<BATCHER_EL_TYPE> > data, struct ArrayBat *arr) =
    true == ((char *)0 <=
             (void*)((ARRAY_BAT_EL_TYPE*)(arr->data))) &*&
    true == ((void*)((ARRAY_BAT_EL_TYPE*)(arr->data) +
                     ARRAY_BAT_CAPACITY) <=
             (char *)UINTPTR_MAX) &*&
    length(data) == ARRAY_BAT_CAPACITY &*&
    struct_ArrayBat_padding(arr) &*&
    bat_arrp(arr->data, ARRAY_BAT_CAPACITY, data);

  predicate arrp_bat_acc(list<list<BATCHER_EL_TYPE> > data, struct ArrayBat *arr,
                         int idx) =
    0 <= idx &*& idx < ARRAY_BAT_CAPACITY &*&
    true == ((char *)0 <=
             (void*)((ARRAY_BAT_EL_TYPE*)(arr->data))) &*&
    true == ((void*)((ARRAY_BAT_EL_TYPE*)(arr->data) +
                     ARRAY_BAT_CAPACITY) <=
             (char *)UINTPTR_MAX) &*&
    length(data) == ARRAY_BAT_CAPACITY &*&
    struct_ArrayBat_padding(arr) &*&
    bat_arrp(arr->data, idx, take(idx, data)) &*&
    bat_arrp((ARRAY_BAT_EL_TYPE*)(arr->data) + idx + 1,
             ARRAY_BAT_CAPACITY - idx - 1, drop(idx+1, data));
  @*/


#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY_BAT_EL_TYPE array_bat_model_cell;
int array_bat_allocated_index;
int array_bat_index_allocated;
struct ArrayBat *array_bat_initialized;
int array_bat_cell_is_exposed = 1;

void array_bat_init(struct ArrayBat *arr_out)
{
  //No need to trace, since it is called from inside the
  // array2_init, which is traced. the spec for array2_init will
  // provide the necessary predicates, whilst array_bat_init is called
  // in the formally verified domain.

  if (!array_bat_cell_is_exposed)
    klee_allow_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE));
  klee_make_symbolic(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array_bat_model_cell");
  array_bat_index_allocated = 0;
  ARRAY_BAT_EL_INIT(&array_bat_model_cell);
  array_bat_initialized = arr_out;
  klee_forbid_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array bat private state");
  array_bat_cell_is_exposed = 0;
}

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_BAT_EL_TYPE));
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayBat), "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_bat_initialized);
  if (array_bat_index_allocated) {
    klee_assert(index == array_bat_allocated_index);
  } else {
    array_bat_allocated_index = index;
    array_bat_index_allocated = 1;
  }
  klee_allow_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE));
  array_bat_cell_is_exposed = 1;
  return &array_bat_model_cell;
}

void array_bat_end_access(struct ArrayBat *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayBat), "arr");
  klee_assert(array_bat_index_allocated);
  klee_assert(arr == array_bat_initialized);

  klee_forbid_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array bat private state");
  array_bat_cell_is_exposed = 0;
  //nothing
}

#else//KLEE_VERIFICATION

/*@ predicate ptrs_eq(ARRAY_BAT_EL_TYPE* p1, int l, ARRAY_BAT_EL_TYPE* p2) =
      p1 == p2 + l;
  @*/
/*@
  lemma void append_to_arr(ARRAY_BAT_EL_TYPE* arr, ARRAY_BAT_EL_TYPE* el)
  requires bat_arrp(arr, ?len, ?lst) &*& batcherpp(?v, el) &*&
           el == (arr + len) &*& len == length(lst);
  ensures bat_arrp(arr, len+1, append(lst, cons(v, nil)));
  {
    close ptrs_eq(el, len, arr);
    open bat_arrp(arr, len, lst);
    open ptrs_eq(el, len, arr);
    assert(el == arr + len);
    switch(lst) {
      case nil:
        close bat_arrp(arr+1, 0, nil);
        close bat_arrp(arr, 1, cons(v, nil));
      case cons(h,t):
        append_to_arr(arr+1, el);
        close bat_arrp(arr, len+1, append(lst, cons(v, nil)));
    }
  }
  @*/

/*@
  predicate upperbounded_ptr(void* p) = true == ((p) <= (char *)UINTPTR_MAX);
  @*/
void array_bat_init(struct ArrayBat *arr_out)
/*@ requires chars((void*)(arr_out),
                   ARRAY_BAT_CAPACITY*sizeof(ARRAY_BAT_EL_TYPE), _) &*&
             struct_ArrayBat_padding(arr_out); @*/
//@ ensures arrp_bat(_, arr_out);
{
  int i;
  //@ close bat_arrp(arr_out->data, 0, nil);
  //@ close upperbounded_ptr((ARRAY_BAT_EL_TYPE*)(arr_out->data) + 0);
  for (i = 0; i < ARRAY_BAT_CAPACITY; ++i)
    /*@
      invariant 0 <= i &*& i <= ARRAY_BAT_CAPACITY &*&
                true == ((char *)0 <=
                         (void*)((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i)) &*&
                upperbounded_ptr((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i) &*&
                bat_arrp(arr_out->data, i, ?lst) &*&
                length(lst) == i &*&
                chars((void*)((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i),
                      sizeof(ARRAY_BAT_EL_TYPE)*
                      (ARRAY_BAT_CAPACITY-i), _);
      @*/
    //@ decreases ARRAY_BAT_CAPACITY - i;
  {
    //@ open upperbounded_ptr((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
    //@ assert i < ARRAY_BAT_CAPACITY;
    //@ chars_limits((void*)((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i));
    //@ assert bat_arrp(arr_out->data, i, ?xxx);

    //@ assert 1 <= ARRAY_BAT_CAPACITY-i;
    //@ mul_mono(1, ARRAY_BAT_CAPACITY-i, sizeof(ARRAY_BAT_EL_TYPE));
    /*@ chars_split((void*)((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i),
                    sizeof(ARRAY_BAT_EL_TYPE));
      @*/
    //@ close_struct((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
    ARRAY_BAT_EL_INIT((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
    //@ assert batcherp(?xx, (ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
    //@ close batcherpp(xx, (ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
    /*@ append_to_arr((ARRAY_BAT_EL_TYPE*)(arr_out->data),
                      (ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
      @*/
    //@ close upperbounded_ptr((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i + 1);
  }
  //@ open upperbounded_ptr((ARRAY_BAT_EL_TYPE*)(arr_out->data) + i);
  //@ assert i == ARRAY_BAT_CAPACITY;
  //@ assert bat_arrp(arr_out->data, ARRAY_BAT_CAPACITY, ?lst);
  //@ close arrp_bat(lst, arr_out);
}

/*@
  lemma void extract_by_index(ARRAY_BAT_EL_TYPE* arr, int idx)
  requires bat_arrp(arr, ?len, ?lst) &*& 0 <= idx &*& idx < len;
  ensures bat_arrp(arr, idx, take(idx, lst)) &*&
          batcherpp(nth(idx, lst), arr + idx) &*&
          bat_arrp(arr+idx+1, len - idx - 1, drop(idx+1,lst));
  {
    open bat_arrp(arr, len, lst);
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
          close bat_arrp(arr, 0, nil);
        } else {
          extract_by_index(arr+1, idx-1);
          close bat_arrp(arr, idx, take(idx, lst));
        }
    }
  }
  @*/

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index)
//@ requires arrp_bat(?lst, arr) &*& 0 <= index &*& index < ARRAY_BAT_CAPACITY;
/*@ ensures arrp_bat_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_bat(arr, index) &*&
            batcherp(nth(index, lst), result) &*&
            length(nth(index, lst)) < BATCHER_CAPACITY; @*/
{
  //@ open arrp_bat(lst, arr);
  //@ extract_by_index(arr->data, index);
  //@ mul_mono_strict(index, ARRAY_BAT_CAPACITY, sizeof(ARRAY_BAT_EL_TYPE));
  return (ARRAY_BAT_EL_TYPE*)(arr->data) + index;
  //@ close arrp_bat_acc(lst, arr, index);
  //@ open batcherpp(nth(index, lst), (ARRAY_BAT_EL_TYPE*)(arr->data) + index);
}

/*@
  lemma void glue_array(ARRAY_BAT_EL_TYPE* arr, int idx,
                        list<list<BATCHER_EL_TYPE> > lst)
  requires bat_arrp(arr, idx, take(idx, lst)) &*&
           batcherpp(nth(idx, lst), arr + idx) &*&
           bat_arrp(arr+idx+1, length(lst) - idx - 1,
                           drop(idx+1,lst)) &*&
           0 <= idx &*& idx < length(lst);
  ensures bat_arrp(arr, length(lst), lst);
  {
    open bat_arrp(arr, idx, take(idx, lst));
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
        } else {
          glue_array(arr+1, idx-1, t);
        }
    }
    close bat_arrp(arr, length(lst), lst);
  }
  @*/
void array_bat_end_access(struct ArrayBat *arr)
/*@ requires arrp_bat_acc(?lst, arr, ?index) &*&
             batcherp(?x, arrp_the_missing_cell_bat(arr, index)) &*&
             length(x) < BATCHER_CAPACITY; @*/
//@ ensures arrp_bat(update(index, x, lst), arr);
{
  //@ open arrp_bat_acc(lst, arr, index);
  //@ take_update_unrelevant(index, index, x, lst);
  //@ nth_update(index, index, x, lst);
  //@ drop_update_unrelevant(index+1, index, x, lst);
  //@ close batcherpp(x, arrp_the_missing_cell_bat(arr, index));
  //@ glue_array(arr->data, index, update(index, x, lst));
  IGNORE(arr);
  //@ close arrp_bat(update(index, x, lst), arr);
}

/* @
   //TODO
  lemma void construct_bat_element(ARRAY_BAT_EL_TYPE *p)
  requires p->len |-> ?l &*&
           pointers((void*)&p->batch, ARRAY_BAT_CAPACITY, _) &*&
           struct_Batcher_padding(p);
  ensures batcherpp(_, p);
  {
    
  }
  @*/

#endif//KLEE_VERIFICATION

#endif//_ARRAY_BAT_IMPL_H_INCLUDED_
