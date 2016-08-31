#include "array-rq.h"

static void lcore_rx_queue_init(struct lcore_rx_queue *cell)
{
#ifdef KLEE_VERIFICATION
  klee_assume(0 <= cell->port_id);
  klee_assume(cell->port_id < RTE_MAX_ETHPORTS);
#else//KLEE_VERIFICATION
  IGNORE(cell);
#endif//KLEE_VERIFICATION
}

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
