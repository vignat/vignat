#ifndef _ARRAY3_H_INCLUDED_
#define _ARRAY3_H_INCLUDED_

#ifndef ARRAY3_EL_TYPE
#  error "Must define the array3 element type."
#endif//ARRAY3_EL_TYPE

#ifndef ARRAY3_CAPACITY
#  error "Must define the array3 capacity."
#endif//ARRAY3_CAPACITY

#ifndef ARRAY3_EL_INIT
#  error "Must define the array1 element initializer function."
#endif//ARRAY3_EL_INIT


struct Array3;

// In-place initialization
void array3_init(struct Array3 *arr_out);
ARRAY3_EL_TYPE *array3_begin_access(struct Array3 *arr, int index);
void array3_end_access(struct Array3 *arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct Array3
{
  char dummy;
};

ARRAY3_EL_TYPE array3_model_cell;
int array3_allocated_index;
int array3_index_allocated;
struct Array3 *array3_initialized;

void array3_init(struct Array3 *arr_out)
{
  // No need for tracing, as it is a nested call in the
  // formally verified domain.
  /* klee_trace_ret(); */
  /* klee_trace_param_i32((uint32_t)arr_out, "arr_out"); */
  /* klee_make_symbolic(&array3_model_cell, sizeof(ARRAY3_EL_TYPE), */
  /*                    "array3_model_cell"); */
  array3_index_allocated = 0;
  ARRAY3_EL_INIT(&array3_model_cell);
  array3_initialized = arr_out;
}

void array3_reset(struct Array3 *arr)
{
  // No need for tracing, this is a shadow control function.
  array3_index_allocated = 0;
  ARRAY3_EL_INIT(&array3_model_cell);
  array3_initialized = arr;
}

ARRAY3_EL_TYPE *array3_begin_access(struct Array3 *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY3_EL_TYPE));
  ARRAY3_EL_TRACE_BREAKDOWN;
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array3_initialized);
  if (array3_index_allocated) {
    klee_assert(index == array3_allocated_index);
  } else {
    array3_allocated_index = index;
    array3_index_allocated = 1;
  }
  return &array3_model_cell;
}

void array3_end_access(struct Array3 *arr)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array3_index_allocated);
  klee_assert(arr == array3_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

struct Array3
{
  ARRAY3_EL_TYPE data[ARRAY3_CAPACITY];
};

void array3_init(struct Array3 *arr_out)
{
  for (int i = 0; i < ARRAY3_CAPACITY; ++i) {
    ARRAY3_EL_INIT(arr_out->data[i]);
  }
}

ARRAY3_EL_TYPE *array3_begin_access(struct Array3 *arr, int index)
{
  return arr->data + index;
}

void array3_end_access(struct Array3 *arr)
{
  (void)arr;
  //nothing
}

#endif//KLEE_VERIFICATION

#endif//_ARRAY3_H_INCLUDED_
