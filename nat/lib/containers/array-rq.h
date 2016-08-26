#ifndef _ARRAY_RQ_H_INCLUDED_
#define _ARRAY_RQ_H_INCLUDED_

#include <stdint.h>
#include "lib/ignore.h"

#define MAX_RX_QUEUE_PER_LCORE 16

struct lcore_rx_queue {
  uint8_t port_id;
  uint8_t queue_id;
}
#ifdef _NO_VERIFAST_
  __rte_cache_aligned;
#else//_NO_VERIFAST_
;
#endif//_NO_VERIFAST_

static void lcore_rx_queue_init(struct lcore_rx_queue *cell)
{
#ifdef KLEE_VERIFICATION
  klee_assume(0 <= cell->port_id);
  klee_assume(cell->port_id < RTE_MAX_ETHPORTS);
#else//KLEE_VERIFICATION
  IGNORE(cell);
#endif//KLEE_VERIFICATION
}

#define ARRAY_RQ_EL_TYPE struct lcore_rx_queue
#define ARRAY_RQ_CAPACITY MAX_RX_QUEUE_PER_LCORE
#define ARRAY_RQ_EL_INIT lcore_rx_queue_init
#define ARRAY_RQ_EL_TRACE_BREAKDOWN {                                   \
    klee_trace_ret_ptr_field(offsetof(struct lcore_rx_queue, port_id),  \
                             sizeof(uint8_t), "port_id");               \
    klee_trace_ret_ptr_field(offsetof(struct lcore_rx_queue, queue_id), \
                             sizeof(uint8_t), "queue_id");              \
  }

struct ArrayRq;

/*@
  inductive rx_queuei = rx_queuei(int,int);
  predicate rx_queuep(rx_queuei rq, struct lcore_rx_queue *lrq);
  predicate some_rx_queuep(struct lcore_rx_queue *lrq) = rx_queuep(_, lrq);
  @*/

/*@
  predicate arrp_rq(list<rx_queuei> data, struct ArrayRq *arr);
  predicate arrp_rq_acc(list<rx_queuei> data, struct ArrayRq *arr, int idx);

  fixpoint ARRAY_RQ_EL_TYPE *arrp_the_missing_cell_rq(struct ArrayRq *arr,
                                                      int idx);

  lemma void construct_rq_element(ARRAY_RQ_EL_TYPE *p);
  requires p->port_id |-> ?pid &*&
           0 <= pid &*& pid <= RTE_MAX_ETHPORTS &*&
           p->queue_id |-> _ &*&
           struct_lcore_rx_queue_padding(p);
  ensures rx_queuep(_, p);
  @*/

// In-place initialization
void array_rq_init(struct ArrayRq *arr_out);
ARRAY_RQ_EL_TYPE *array_rq_begin_access(struct ArrayRq *arr, int index);
//@ requires arrp_rq(?lst, arr) &*& 0 <= index &*& index < ARRAY_RQ_CAPACITY;
/*@ ensures arrp_rq_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_rq(arr, index) &*&
            rx_queuep(nth(index, lst), result); @*/

void array_rq_end_access(struct ArrayRq *arr);
/*@ requires arrp_rq_acc(?lst, arr, ?idx) &*&
             rx_queuep(?rq, arrp_the_missing_cell_rq(arr, idx)); @*/
//@ ensures arrp_rq(update(idx, rq, lst), arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct ArrayRq
{
  char dummy;
};

ARRAY_RQ_EL_TYPE array_rq_model_cell;
int array_rq_allocated_index;
int array_rq_index_allocated;
struct ArrayRq *array_rq_initialized;

void array_rq_init(struct ArrayRq *arr_out)
{
  // No need for tracing, as it is a nested call in the
  // formally verified domain.
  /* klee_trace_ret(); */
  /* klee_trace_param_i32((uint32_t)arr_out, "arr_out"); */
  klee_make_symbolic(&array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array_rq_model_cell");
  array_rq_index_allocated = 0;
  ARRAY_RQ_EL_INIT(&array_rq_model_cell);
  array_rq_initialized = arr_out;
}

void array_rq_reset(struct ArrayRq *arr)
{
  // No need for tracing, this is a shadow control function.
  klee_make_symbolic(&array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE),
                     "array_rq_model_cell");
  array_rq_index_allocated = 0;
  ARRAY_RQ_EL_INIT(&array_rq_model_cell);
  array_rq_initialized = arr;
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
  return &array_rq_model_cell;
}

void array_rq_end_access(struct ArrayRq *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayRq), "arr");
  klee_assert(array_rq_index_allocated);
  klee_assert(arr == array_rq_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

struct ArrayRq
{
  ARRAY_RQ_EL_TYPE data[ARRAY_RQ_CAPACITY];
};

#ifdef _NO_VERIFAST_

void array_rq_init(struct ArrayRq *arr_out)
{
  int i;
  for (i = 0; i < ARRAY_RQ_CAPACITY; ++i) {
    ARRAY_RQ_EL_INIT(&arr_out->data[i]);
  }
}

ARRAY_RQ_EL_TYPE *array_rq_begin_access(struct ArrayRq *arr, int index)
{
  return arr->data + index;
}

void array_rq_end_access(struct ArrayRq *arr)
{
  (void)arr;
  //nothing
}

#endif//_NO_VERIFAST_

#endif//KLEE_VERIFICATION

#undef ARRAY_RQ_EL_TRACE_BREAKDOWN
#undef ARRAY_RQ_EL_INIT
#undef ARRAY_RQ_CAPACITY
#undef ARRAY_RQ_EL_TYPE

#endif//_ARRAY_RQ_H_INCLUDED_
