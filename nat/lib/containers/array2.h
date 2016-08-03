#ifndef _ARRAY2_H_INCLUDED_
#define _ARRAY2_H_INCLUDED_

#ifndef ARRAY2_EL_TYPE
#  error "Must define the array2 element type."
#endif//ARRAY2_EL_TYPE

#ifndef ARRAY2_CAPACITY
#  error "Must define the array2 capacity."
#endif//ARRAY2_CAPACITY

#ifndef ARRAY2_EL_INIT
#  error "Must define the array1 element initializer function."
#endif//ARRAY2_EL_INIT


struct Array2
{
  ARRAY2_EL_TYPE data[ARRAY2_CAPACITY];
};

// In-place initialization
void array2_init(struct Array2 *arr_out);
ARRAY2_EL_TYPE *array2_begin_access(struct Array2 *arr, int index);
void array2_end_access(struct Array2 *arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY2_EL_TYPE array2_model_cell;
int array2_allocated_index;
int array2_index_allocated;

typedef int (*array2_cell_condition_type)(ARRAY2_EL_TYPE *cell);
array2_cell_condition_type array2_cell_cond = 0;

void array2_set_cell_condition(array2_cell_condition_type cond)
{
  array2_cell_cond = cond;
}

void array2_init(struct Array2 *arr_out)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr_out, "arr_out");
  klee_make_symbolic(&array2_model_cell, sizeof(ARRAY2_EL_TYPE),
                     "array2_model_cell");
  array2_index_allocated = 0;
  klee_assume(array2_cell_cond(&array2_model_cell));
}

ARRAY2_EL_TYPE *array2_begin_access(struct Array2 *arr, int index)
{
  //TODO: trace ptr?
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_trace_param_i32(index, "index");
  if (array2_index_allocated) {
    klee_assert(index == array2_allocated_index);
  } else {
    array2_allocated_index = index;
    array2_index_allocated = 1;
  }
  return &array2_model_cell;
}

void array2_end_access(struct Array2 *arr)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array2_index_allocated);
  //nothing
}

#else//KLEE_VERIFICATION


void array2_init(struct Array2 *arr_out)
{
  for (int i = 0; i < ARRAY2_CAPACITY; ++i) {
    ARRAY2_EL_INIT(arr_out->data[i]);
  }
}

ARRAY2_EL_TYPE *array2_begin_access(struct Array2 *arr, int index)
{
  return arr->data + index;
}

void array2_end_access(struct Array2 *arr)
{
  (void)arr;
  //nothing
}

#endif//KLEE_VERIFICATION

#endif//_ARRAY2_H_INCLUDED_
