#include "array-lcc.h"

static void lcore_conf_condition(struct lcore_conf *cell)
{
#ifdef KLEE_VERIFICATION
  klee_assume(0 < cell->n_rx_queue);
  klee_assume(cell->n_rx_queue < MAX_RX_QUEUE_PER_LCORE);
  array_rq_init(&cell->rx_queue_list);
  array_u16_init(&cell->tx_queue_id);
  array_bat_init(&cell->tx_mbufs);
#else//KLEE_VERIFICATION
  IGNORE(cell);
#endif//KLEE_VERIFICATION
}


// In-place initialization
void array_lcc_init(struct ArrayLcc *arr_out);
/*@ requires chars(arr_out->data,
  sizeof(ARRAY_LCC_EL_TYPE)*ARRAY_LCC_CAPACITY, _);@*/
//@ ensures arrp_lcc(_, arr_out);

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index);
//@ requires arrp_lcc(?lst, arr) &*& 0 <= index &*& index < ARRAY_LCC_CAPACITY;
/*@ ensures arrp_lcc_acc(lst, arr, index) &*&
  result == arrp_the_missing_cell_lcc(arr, index) &*&
  lcore_confp(nth(index, lst), result);
  @*/

void array_lcc_end_access(struct ArrayLcc *arr);
/*@ requires arrp_lcc_acc(?lst, arr, ?idx) &*&
  lcore_confp(?lc, arrp_the_missing_cell_lcc(arr, idx)); @*/
//@ ensures arrp_lcc(update(idx, lc, lst), arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY_LCC_EL_TYPE array_lcc_model_cell;
int array_lcc_allocated_index;
int array_lcc_index_allocated;
struct ArrayLcc *array_lcc_initialized;

void array_lcc_init(struct ArrayLcc *arr_out)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr_out, sizeof(struct ArrayLcc), "arr_out");
  klee_make_symbolic(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "array_lcc_model_cell");
  array_lcc_index_allocated = 0;
  ARRAY_LCC_EL_INIT(&array_lcc_model_cell);
  array_lcc_initialized = arr_out;
}

void array_lcc_reset(struct ArrayLcc *arr)
{
  //Non traceable function.
  klee_assert(arr == array_lcc_initialized);
  klee_make_symbolic(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "array_lcc_model_cell");
  array_lcc_index_allocated = 0;
  ARRAY_LCC_EL_INIT(&array_lcc_model_cell);
}

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_LCC_EL_TYPE));
  ARRAY_LCC_EL_TRACE_BREAKDOWN;
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayLcc), "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_lcc_initialized);
  if (array_lcc_index_allocated) {
    klee_assert(index == array_lcc_allocated_index);
  } else {
    array_lcc_allocated_index = index;
    array_lcc_index_allocated = 1;
  }
  return &array_lcc_model_cell;
}

void array_lcc_end_access(struct ArrayLcc *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayLcc), "arr");
  klee_assert(array_lcc_index_allocated);
  klee_assert(arr == array_lcc_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

void array_lcc_init(struct ArrayLcc *arr_out)
{
  int i;
  for (i = 0; i < ARRAY_LCC_CAPACITY; ++i) {
    ARRAY_LCC_EL_INIT(&((*arr_out).data[i]));
  }
}

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index)
{
  return &((*arr).data[index]);
}

void array_lcc_end_access(struct ArrayLcc *arr)
{
  (void)arr;
  //nothing
}

#endif//_NO_VERIFAST_

#endif//KLEE_VERIFICATION
