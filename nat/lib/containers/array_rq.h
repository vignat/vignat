#ifndef _ARRAY_RQ_H_INCLUDED_
#define _ARRAY_RQ_H_INCLUDED_

#include <stdint.h>
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

void lcore_rx_queue_init(struct lcore_rx_queue *cell)
{
#ifdef KLEE_VERIFICATION
  klee_assume(0 <= cell->port_id);
  klee_assume(cell->port_id < RTE_MAX_ETHPORTS);
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

// In-place initialization
void array_rq_init(struct ArrayRq *arr_out);
ARRAY_RQ_EL_TYPE *array_rq_begin_access(struct ArrayRq *arr, int index);
void array_rq_end_access(struct ArrayRq *arr);

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
  /* klee_make_symbolic(&array_rq_model_cell, sizeof(ARRAY_RQ_EL_TYPE), */
  /*                    "array_rq_model_cell"); */
  array_rq_index_allocated = 0;
  ARRAY_RQ_EL_INIT(&array_rq_model_cell);
  array_rq_initialized = arr_out;
}

void array_rq_reset(struct ArrayRq *arr)
{
  // No need for tracing, this is a shadow control function.
  array_rq_index_allocated = 0;
  ARRAY_RQ_EL_INIT(&array_rq_model_cell);
  array_rq_initialized = arr;
}

ARRAY_RQ_EL_TYPE *array_rq_begin_access(struct ArrayRq *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_RQ_EL_TYPE));
  ARRAY_RQ_EL_TRACE_BREAKDOWN;
  klee_trace_param_i32((uint32_t)arr, "arr");
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
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array_rq_index_allocated);
  klee_assert(arr == array_rq_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

struct ArrayRq
{
  ARRAY_RQ_EL_TYPE data[ARRAY_RQ_CAPACITY];
};

void array_rq_init(struct ArrayRq *arr_out)
{
  for (int i = 0; i < ARRAY_RQ_CAPACITY; ++i) {
    ARRAY_RQ_EL_INIT(arr_out->data[i]);
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
