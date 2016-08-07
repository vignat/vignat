#ifndef _ARRAY_BAT_H_INCLUDED_
#define _ARRAY_BAT_H_INCLUDED_

#include "lib/static-component-params.h"
#include "lib/containers/batcher.h"

#define ARRAY_BAT_EL_TYPE struct Batcher
#define ARRAY_BAT_CAPACITY RTE_MAX_ETHPORTS
#define ARRAY_BAT_EL_INIT batcher_init

struct ArrayBat;

/*@
  //params: list<struct rte_mbuf*> , batcherp
  predicate arrp1(list<list<struct rte_mbuf*> > data, struct ArrayBat* arr);
  predicate arrp1_acc(list<list<struct rte_mbuf*> > data, struct ArrayBat* arr,
                      int idx, ARRAY_BAT_EL_TYPE *el);
  @*/

// In-place initialization
void array_bat_init(struct ArrayBat *arr_out);
//@ requires true;
/* @ requires arr_out->data |-> ?data &*&
             chars(data, ARRAY_BAT_CAPACITY*sizeof(ARRAY_BAT_EL_TYPE), _); @*/
//@ ensures arrp1(_, arr_out);

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index);
//@ requires arrp1(?lst, arr) &*& 0 <= index &*& index < ARRAY_BAT_CAPACITY;
/*@ ensures arrp1_acc(lst, arr, index, result) &*&
            batcherp(nth(index, lst), result); @*/

void array_bat_end_access(struct ArrayBat *arr);
/*@ requires arrp1_acc(?lst, arr, ?index, ?ptr) &*&
             batcherp(?x, ptr); @*/
//@ ensures arrp1(update(index, x, lst), arr);


#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct ArrayBat
{
  char dummy;
};

ARRAY_BAT_EL_TYPE array_bat_model_cell;
int array_bat_allocated_index;
int array_bat_index_allocated;
struct ArrayBat *array_bat_initialized;

void array_bat_init(struct ArrayBat *arr_out)
{
  //No need to trace, since it is called from inside the
  // array2_init, which is traced. the spec for array2_init will
  // provide the necessary predicates, whilst array_bat_init is called
  // in the formally verified domain.
  //klee_trace_ret();
  //klee_trace_param_i32((uint32_t)arr_out, "arr_out");

  klee_make_symbolic(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array_bat_model_cell");
  array_bat_index_allocated = 0;
  ARRAY_BAT_EL_INIT(&array_bat_model_cell);
  array_bat_initialized = arr_out;
}

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_BAT_EL_TYPE));
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_bat_initialized);
  if (array_bat_index_allocated) {
    klee_assert(index == array_bat_allocated_index);
  } else {
    array_bat_allocated_index = index;
    array_bat_index_allocated = 1;
  }
  return &array_bat_model_cell;
}

void array_bat_end_access(struct ArrayBat *arr)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array_bat_index_allocated);
  klee_assert(arr == array_bat_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

struct ArrayBat
{
  struct Batcher data[ARRAY_BAT_CAPACITY];
};

void array_bat_init(struct ArrayBat *arr_out)
{
  int i;
  for (i = 0; i < ARRAY_BAT_CAPACITY; ++i) {
    ARRAY_BAT_EL_INIT(&arr_out->data[i]);
  }
}

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index)
{
  return arr->data + index;
}

void array_bat_end_access(struct ArrayBat *arr)
{
  (void)arr;
  //nothing
}

#endif//_NO_VERIFAST_

#endif//KLEE_VERIFICATION

#undef ARRAY_BAT_EL_TYPE
#undef ARRAY_BAT_CAPACITY
#undef ARRAY_BAT_EL_INIT

#endif//_ARRAY_BAT_H_INCLUDED_
