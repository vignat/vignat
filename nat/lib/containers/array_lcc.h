#ifndef _ARRAY_LCC_H_INCLUDED_
#define _ARRAY_LCC_H_INCLUDED_

#include <stdint.h>
#include "lib/static-component-params.h"
#include "lib/containers/array_rq.h"
#include "lib/containers/array_u16.h"
#include "lib/containers/array_bat.h"

struct lcore_conf {
  uint16_t n_rx_queue;
  struct ArrayRq rx_queue_list;
  struct ArrayU16 tx_queue_id;
  struct ArrayBat tx_mbufs;
}
  #ifdef _NO_VERIFAST_
  __rte_cache_aligned;
#else//_NO_VERIFAST_
;
#endif//_NO_VERIFAST_

void lcore_conf_condition(struct lcore_conf *cell)
{
#ifdef KLEE_VERIFICATION
  klee_assume(0 < cell->n_rx_queue);
  klee_assume(cell->n_rx_queue < MAX_RX_QUEUE_PER_LCORE);
  array_rq_init(&cell->rx_queue_list);
  array_u16_init(&cell->tx_queue_id);
  array_bat_init(&cell->tx_mbufs);
#endif//KLEE_VERIFICATION
}

#define ARRAY_LCC_EL_TYPE struct lcore_conf
#define ARRAY_LCC_CAPACITY RTE_MAX_LCORE
#define ARRAY_LCC_SUFFIX _lconf
#define ARRAY_LCC_EL_INIT lcore_conf_condition
#define ARRAY_LCC_EL_TRACE_BREAKDOWN {                                  \
    klee_trace_ret_ptr_field(offsetof(struct lcore_conf, n_rx_queue),   \
                             sizeof(uint16_t), "n_rx_queue");           \
    klee_trace_ret_ptr_field(offsetof(struct lcore_conf, rx_queue_list), \
                             sizeof(struct ArrayRq), "rx_queue_list");  \
    klee_trace_ret_ptr_field(offsetof(struct lcore_conf, tx_queue_id),  \
                             sizeof(struct ArrayU16), "tx_queue_id");   \
    klee_trace_ret_ptr_field(offsetof(struct lcore_conf, tx_mbufs),     \
                             sizeof(struct ArrayBat), "tx_mbufs");      \
  }

struct ArrayLcc;

// In-place initialization
void array_lcc_init(struct ArrayLcc *arr_out);
ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index);
void array_lcc_end_access(struct ArrayLcc *arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct ArrayLcc
{
  char dummy;
};

ARRAY_LCC_EL_TYPE array_lcc_model_cell;
int array_lcc_allocated_index;
int array_lcc_index_allocated;
struct ArrayLcc *array_lcc_initialized;

void array_lcc_init(struct ArrayLcc *arr_out)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr_out, "arr_out");
  klee_make_symbolic(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "array_lcc_model_cell");
  array_lcc_index_allocated = 0;
  ARRAY_LCC_EL_INIT(&array_lcc_model_cell);
  array_lcc_initialized = arr_out;
}

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_LCC_EL_TYPE));
  ARRAY_LCC_EL_TRACE_BREAKDOWN;
  klee_trace_param_i32((uint32_t)arr, "arr");
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
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array_lcc_index_allocated);
  klee_assert(arr == array_lcc_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

struct ArrayLcc
{
  ARRAY_LCC_EL_TYPE data[ARRAY_LCC_CAPACITY];
};

void array_lcc_init(struct ArrayLcc *arr_out)
{
  for (int i = 0; i < ARRAY_LCC_CAPACITY; ++i) {
    ARRAY_LCC_EL_INIT(arr_out->data[i]);
  }
}

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index)
{
  return arr->data + index;
}

void array_lcc_end_access(struct ArrayLcc *arr)
{
  (void)arr;
  //nothing
}

#endif//_NO_VERIFAST_

#endif//KLEE_VERIFICATION

#undef ARRAY_LCC_EL_TRACE_BREAKDOWN
#undef ARRAY_LCC_EL_INIT
#undef ARRAY_LCC_SUFFIX
#undef ARRAY_LCC_CAPACITY
#undef ARRAY_LCC_EL_TYPE

#endif//_ARRAY_LCC_H_INCLUDED_
