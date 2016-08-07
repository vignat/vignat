#ifndef _ARRAY_U16_H_INCLUDED_
#define _ARRAY_U16_H_INCLUDED_

#include <stdint.h>
#include "lib/static-component-params.h"

#define ARRAY_U16_EL_TYPE uint16_t
#define ARRAY_U16_CAPACITY RTE_MAX_ETHPORTS
#define ARRAY_U16_EL_INIT (void)

struct ArrayU16;

// In-place initialization
void array_u16_init(struct ArrayU16 *arr_out);
ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index);
void array_u16_end_access(struct ArrayU16 *arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct ArrayU16
{
  char dummy;
};

ARRAY_U16_EL_TYPE array_u16_model_cell;
int array_u16_allocated_index;
int array_u16_index_allocated;
struct ArrayU16 *array_u16_initialized;

void array_u16_init(struct ArrayU16 *arr_out)
{
  // No need for tracing, as it is a nested call in the
  // formally verified domain.
  /* klee_trace_ret(); */
  /* klee_trace_param_i32((uint32_t)arr_out, "arr_out"); */
  /* klee_make_symbolic(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE), */
  /*                    "array_u16_model_cell"); */
  array_u16_index_allocated = 0;
  ARRAY_U16_EL_INIT(&array_u16_model_cell);
  array_u16_initialized = arr_out;
}

void array_u16_reset(struct ArrayU16 *arr)
{
  // No need for tracing, this is a shadow control function.
  array_u16_index_allocated = 0;
  ARRAY_U16_EL_INIT(&array_u16_model_cell);
  array_u16_initialized = arr;
}

ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_U16_EL_TYPE));
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_u16_initialized);
  if (array_u16_index_allocated) {
    klee_assert(index == array_u16_allocated_index);
  } else {
    array_u16_allocated_index = index;
    array_u16_index_allocated = 1;
  }
  return &array_u16_model_cell;
}

void array_u16_end_access(struct ArrayU16 *arr)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array_u16_index_allocated);
  klee_assert(arr == array_u16_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

struct ArrayU16
{
  ARRAY_U16_EL_TYPE data[ARRAY_U16_CAPACITY];
};

void array_u16_init(struct ArrayU16 *arr_out)
{
  for (int i = 0; i < ARRAY_U16_CAPACITY; ++i) {
    ARRAY_U16_EL_INIT(&arr_out->data[i]);
  }
}

ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index)
{
  return arr->data + index;
}

void array_u16_end_access(struct ArrayU16 *arr)
{
  (void)arr;
  //nothing
}

#endif//_NO_VERIFAST_

#endif//KLEE_VERIFICATION

#undef ARRAY_U16_EL_INIT
#undef ARRAY_U16_CAPACITY
#undef ARRAY_U16_EL_TYPE

#endif//_ARRAY_U16_H_INCLUDED_
