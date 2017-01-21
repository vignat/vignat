#ifndef _ARRAY_RQ_IMPL_H_INCLUDED_
#define _ARRAY_RQ_IMPL_H_INCLUDED_

#include "array-rq.h"

//@ #include "stdex.gh"
//@ #include "arith.gh"
//@ #include "nat.gh"

/*@
  predicate rx_queue_arrp(struct lcore_rx_queue *lrq,
                          int len, list<rx_queuei> data) =
     switch(data) {
       case nil: return len == 0;
       case cons(h,t):
         return rx_queuep(h, lrq) &*&
                rx_queue_arrp(lrq+1,len-1,t);
     };

  predicate arrp_rq(list<rx_queuei> data, struct ArrayRq *arr) =
    true == ((char *)0 <=
            (void*)((ARRAY_RQ_EL_TYPE*)(arr->data))) &*&
    true == ((void*)((ARRAY_RQ_EL_TYPE*)(arr->data) +
                    ARRAY_RQ_CAPACITY) <=
            (char *)UINTPTR_MAX) &*&
    length(data) == ARRAY_RQ_CAPACITY &*&
    struct_ArrayRq_padding(arr) &*&
    rx_queue_arrp(arr->data, ARRAY_RQ_CAPACITY, data);

  predicate arrp_rq_acc(list<rx_queuei> data, struct ArrayRq *arr, int idx) =
    0 <= idx &*& idx < ARRAY_RQ_CAPACITY &*&
    true == ((char *)0 <=
             (void*)((ARRAY_RQ_EL_TYPE*)(arr->data))) &*&
    true == ((void*)((ARRAY_RQ_EL_TYPE*)(arr->data) +
                     ARRAY_RQ_CAPACITY) <=
             (char *)UINTPTR_MAX) &*&
    length(data) == ARRAY_RQ_CAPACITY &*&
    struct_ArrayRq_padding(arr) &*&
    rx_queue_arrp(arr->data, idx, take(idx, data)) &*&
    rx_queue_arrp((ARRAY_RQ_EL_TYPE*)(arr->data)+idx+1,
                  ARRAY_RQ_CAPACITY - idx - 1, drop(idx+1,data));
  @*/

static void lcore_rx_queue_init(struct lcore_rx_queue *cell)
//@ requires chars((void*)cell, sizeof(struct lcore_rx_queue), _);
//@ ensures rx_queuep(_, cell);
{
  //@ close_struct(cell);
#ifdef KLEE_VERIFICATION
  klee_assume(0 <= cell->port_id);
  klee_assume(cell->port_id < RTE_MAX_ETHPORTS);
#else//KLEE_VERIFICATION
  cell->port_id = 0;
#endif//KLEE_VERIFICATION
  //@ close rx_queuep(rx_queuei(cell->port_id, cell->queue_id), cell);
}

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY_RQ_EL_TYPE *array_rq_model_cell = 0;
int array_rq_allocated_index;
int array_rq_index_allocated;
struct ArrayRq *array_rq_initialized;
int array_rq_cell_is_exposed = 1;

void array_rq_init(struct ArrayRq *arr_out)
{
  // No need for tracing, as it is a nested call in the
  // formally verified domain.
  /* klee_trace_ret(); */
  /* klee_trace_param_i32((uint32_t)arr_out, "arr_out"); */
  array_rq_model_cell = malloc(sizeof(ARRAY_RQ_EL_TYPE));
  klee_make_symbolic(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array_rq_model_cell");
  array_rq_index_allocated = 0;
  ARRAY_RQ_EL_INIT(array_rq_model_cell);
  array_rq_initialized = arr_out;
  array_rq_cell_is_exposed = 0;
  klee_forbid_access(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array rq private state");
}

void array_rq_reset(struct ArrayRq *arr)
{
  // No need for tracing, this is a shadow control function.
  klee_assert(!array_rq_cell_is_exposed);
  // Allocate a new cell each time, this way the returned pointers will never
  // collide.
  array_rq_model_cell = malloc(sizeof(ARRAY_RQ_EL_TYPE));
  klee_make_symbolic(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array_rq_model_cell");
  array_rq_index_allocated = 0;
  ARRAY_RQ_EL_INIT(array_rq_model_cell);
  array_rq_initialized = arr;
  klee_forbid_access(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array rq private state");
}

ARRAY_RQ_EL_TYPE *array_rq_begin_access(struct ArrayRq *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_RQ_EL_TYPE));
  ARRAY_RQ_EL_TRACE_BREAKDOWN;
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayRq), "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_rq_initialized);
  if (array_rq_index_allocated) {
    klee_assert(index == array_rq_allocated_index);
  } else {
    array_rq_allocated_index = index;
    array_rq_index_allocated = 1;
  }
  klee_allow_access(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE));
  array_rq_cell_is_exposed = 1;
  return array_rq_model_cell;
}

void array_rq_end_access(struct ArrayRq *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayRq), "arr");
  klee_assert(array_rq_index_allocated);
  klee_assert(arr == array_rq_initialized);
  klee_trace_extra_ptr(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                       "returned_rq_cell");
  ARRAY_RQ_EL_TRACE_EP_BREAKDOWN(array_rq_model_cell);
  klee_forbid_access(array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array rq private state");
  array_rq_cell_is_exposed = 0;
  //nothing
}

#else//KLEE_VERIFICATION

/*@ predicate ptrs_eq(ARRAY_RQ_EL_TYPE* p1, int l, ARRAY_RQ_EL_TYPE* p2) =
      p1 == p2 + l;
  @*/
/*@
  lemma void append_to_arr(ARRAY_RQ_EL_TYPE* arr, ARRAY_RQ_EL_TYPE* el)
  requires rx_queue_arrp(arr, ?len, ?lst) &*& rx_queuep(?v, el) &*&
           el == (arr + len) &*& len == length(lst);
  ensures rx_queue_arrp(arr, len+1, append(lst, cons(v, nil)));
  {
    close ptrs_eq(el, len, arr);
    open rx_queue_arrp(arr, len, lst);
    open ptrs_eq(el, len, arr);
    assert(el == arr + len);
    switch(lst) {
      case nil:
        close rx_queue_arrp(arr+1, 0, nil);
        close rx_queue_arrp(arr, 1, cons(v, nil));
      case cons(h,t):
        append_to_arr(arr+1, el);
        close rx_queue_arrp(arr, len+1, append(lst, cons(v, nil)));
    }
  }
  @*/

/*@
  predicate upperbounded_ptr(void* p) = true == ((p) <= (char *)UINTPTR_MAX);
  @*/
void array_rq_init(struct ArrayRq *arr_out)
/*@ requires chars((void*)(arr_out),
                   16*sizeof(struct lcore_rx_queue), _) &*&
             struct_ArrayRq_padding(arr_out); @*/
//@ ensures arrp_rq(_, arr_out);
{
  int i;
  //@ close rx_queue_arrp(arr_out->data, 0, nil);
  //@ close upperbounded_ptr((ARRAY_RQ_EL_TYPE*)(arr_out->data) + 0);
  for (i = 0; i < ARRAY_RQ_CAPACITY; ++i)
    /*@
      invariant 0 <= i &*& i <= ARRAY_RQ_CAPACITY &*&
                true == ((char *)0 <=
                         (void*)((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i)) &*&
                upperbounded_ptr((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i) &*&
                rx_queue_arrp(arr_out->data, i, ?lst) &*&
                length(lst) == i &*&
                chars((void*)((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i),
                      sizeof(ARRAY_RQ_EL_TYPE)*
                      (ARRAY_RQ_CAPACITY-i), _);
      @*/
    //@ decreases ARRAY_RQ_CAPACITY - i;
  {
    //@ open upperbounded_ptr((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i);
    //@ assert i < ARRAY_RQ_CAPACITY;
    //@ chars_limits((void*)((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i));
    //@ assert rx_queue_arrp(arr_out->data, i, ?xxx);

    //@ assert 1 <= ARRAY_RQ_CAPACITY-i;
    //@ mul_mono(1, ARRAY_RQ_CAPACITY-i, sizeof(ARRAY_RQ_EL_TYPE));
    /*@ chars_split((void*)((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i),
                    sizeof(ARRAY_RQ_EL_TYPE));
      @*/
    ARRAY_RQ_EL_INIT((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i);
    //@ assert rx_queuep(?xx, (ARRAY_RQ_EL_TYPE*)(arr_out->data) + i);
    /*@ append_to_arr((ARRAY_RQ_EL_TYPE*)(arr_out->data),
                      (ARRAY_RQ_EL_TYPE*)(arr_out->data) + i);
      @*/
    //@ close upperbounded_ptr((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i + 1);
  }
  //@ open upperbounded_ptr((ARRAY_RQ_EL_TYPE*)(arr_out->data) + i);
  //@ assert i == ARRAY_RQ_CAPACITY;
  //@ assert rx_queue_arrp(arr_out->data, ARRAY_RQ_CAPACITY, ?lst);
  //@ close arrp_rq(lst, arr_out);
}

/*@
  lemma void extract_by_index(ARRAY_RQ_EL_TYPE* arr, int idx)
  requires rx_queue_arrp(arr, ?len, ?lst) &*& 0 <= idx &*& idx < len;
  ensures rx_queue_arrp(arr, idx, take(idx, lst)) &*&
          rx_queuep(nth(idx, lst), arr + idx) &*&
          rx_queue_arrp(arr+idx+1, len - idx - 1, drop(idx+1,lst));
  {
    open rx_queue_arrp(arr, len, lst);
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
          close rx_queue_arrp(arr, 0, nil);
        } else {
          extract_by_index(arr+1, idx-1);
          close rx_queue_arrp(arr, idx, take(idx, lst));
        }
    }
  }
  @*/

ARRAY_RQ_EL_TYPE *array_rq_begin_access(struct ArrayRq *arr, int index)
//@ requires arrp_rq(?lst, arr) &*& 0 <= index &*& index < ARRAY_RQ_CAPACITY;
/*@ ensures arrp_rq_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_rq(arr, index) &*&
            rx_queuep(nth(index, lst), result); @*/
{
  //@ open arrp_rq(lst, arr);
  //@ extract_by_index(arr->data, index);
  //@ mul_mono_strict(index, ARRAY_RQ_CAPACITY, sizeof(ARRAY_RQ_EL_TYPE));
  return (ARRAY_RQ_EL_TYPE*)(arr->data) + index;
  //@ close arrp_rq_acc(lst, arr, index);
}

/*@
  lemma void glue_array(ARRAY_RQ_EL_TYPE* arr, int idx,
                        list<rx_queuei> lst)
  requires rx_queue_arrp(arr, idx, take(idx, lst)) &*&
           rx_queuep(nth(idx, lst), arr + idx) &*&
           rx_queue_arrp(arr+idx+1, length(lst) - idx - 1,
                           drop(idx+1,lst)) &*&
           0 <= idx &*& idx < length(lst);
  ensures rx_queue_arrp(arr, length(lst), lst);
  {
    open rx_queue_arrp(arr, idx, take(idx, lst));
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
        } else {
          glue_array(arr+1, idx-1, t);
        }
    }
    close rx_queue_arrp(arr, length(lst), lst);
  }
  @*/

void array_rq_end_access(struct ArrayRq *arr)
/*@ requires arrp_rq_acc(?lst, arr, ?idx) &*&
             rx_queuep(?rq, arrp_the_missing_cell_rq(arr, idx)); @*/
//@ ensures arrp_rq(update(idx, rq, lst), arr);
{
  //@ open arrp_rq_acc(lst, arr, idx);
  //@ take_update_unrelevant(idx, idx, rq, lst);
  //@ nth_update(idx, idx, rq, lst);
  //@ drop_update_unrelevant(idx+1, idx, rq, lst);
  //@ glue_array(arr->data, idx, update(idx, rq, lst));
  IGNORE(arr);
  //@ close arrp_rq(update(idx, rq, lst), arr);
}

/* @
  lemma void construct_rq_element(ARRAY_RQ_EL_TYPE *p)
  requires p->port_id |-> ?pid &*&
           0 <= pid &*& pid < RTE_MAX_ETHPORTS &*&
           p->queue_id |-> _ &*&
           struct_lcore_rx_queue_padding(p);
  ensures rx_queuep(_, p);
  {
    close rx_queuep(rx_queuei(pid,p->queue_id), p);
  }
  @*/

#endif//KLEE_VERIFICATION

#endif//_ARRAY_RQ_IMPL_H_INCLUDED_
