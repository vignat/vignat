#ifndef _ARRAY4_H_INCLUDED_
#define _ARRAY4_H_INCLUDED_

#ifndef ARRAY4_EL_TYPE
#  error "Must define the array4 element type."
#endif//ARRAY4_EL_TYPE

#ifndef ARRAY4_CAPACITY
#  error "Must define the array4 capacity."
#endif//ARRAY4_CAPACITY

#ifndef ARRAY4_EL_INIT
#  error "Must define the array1 element initializer function."
#endif//ARRAY4_EL_INIT


struct Array4;

// In-place initialization
void array4_init(struct Array4 *arr_out);
ARRAY4_EL_TYPE *array4_begin_access(struct Array4 *arr, int index);
void array4_end_access(struct Array4 *arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct Array4
{
  char dummy;
};

ARRAY4_EL_TYPE array4_model_cell;
int array4_allocated_index;
int array4_index_allocated;
struct Array4 *array4_initialized;

void array4_init(struct Array4 *arr_out)
{
  // No need for tracing, as it is a nested call in the
  // formally verified domain.
  /* klee_trace_ret(); */
  /* klee_trace_param_i32((uint32_t)arr_out, "arr_out"); */
  /* klee_make_symbolic(&array4_model_cell, sizeof(ARRAY4_EL_TYPE), */
  /*                    "array4_model_cell"); */
  array4_index_allocated = 0;
  ARRAY4_EL_INIT(&array4_model_cell);
  array4_initialized = arr_out;
}

void array4_reset(struct Array4 *arr)
{
  // No need for tracing, this is a shadow control function.
  array4_index_allocated = 0;
  ARRAY4_EL_INIT(&array4_model_cell);
  array4_initialized = arr;
}

ARRAY4_EL_TYPE *array4_begin_access(struct Array4 *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY4_EL_TYPE));
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array4_initialized);
  if (array4_index_allocated) {
    klee_assert(index == array4_allocated_index);
  } else {
    array4_allocated_index = index;
    array4_index_allocated = 1;
  }
  return &array4_model_cell;
}

void array4_end_access(struct Array4 *arr)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array4_index_allocated);
  klee_assert(arr == array4_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

struct Array4
{
  ARRAY4_EL_TYPE data[ARRAY4_CAPACITY];
};

void array4_init(struct Array4 *arr_out)
{
  for (int i = 0; i < ARRAY4_CAPACITY; ++i) {
    ARRAY4_EL_INIT(arr_out->data[i]);
  }
}

ARRAY4_EL_TYPE *array4_begin_access(struct Array4 *arr, int index)
{
  return arr->data + index;
}

void array4_end_access(struct Array4 *arr)
{
  (void)arr;
  //nothing
}

#endif//KLEE_VERIFICATION

#endif//_ARRAY4_H_INCLUDED_
