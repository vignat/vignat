#include "array-u16.h"

// In-place initialization
void array_u16_init(struct ArrayU16 *arr_out);
ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index);
//@ requires arrp_u16(?lst, arr) &*& 0 <= index &*& index < ARRAY_U16_CAPACITY;
/*@ ensures arrp_u16_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_u16(arr, index) &*&
            u_short_integer(result, nth(index, lst)); @*/
void array_u16_end_access(struct ArrayU16 *arr);
/*@ requires arrp_u16_acc(?lst, arr, ?idx) &*&
             u_short_integer(arrp_the_missing_cell_u16(arr, idx), ?u16); @*/
//@ ensures arrp_u16(update(idx, u16, lst), arr);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY_U16_EL_TYPE array_u16_model_cell;
int array_u16_allocated_index;
int array_u16_index_allocated;
struct ArrayU16 *array_u16_initialized;
int array_u16_cell_is_exposed = 1;

void array_u16_init(struct ArrayU16 *arr_out)
{
  // No need for tracing, as it is a nested call in the
  // formally verified domain.
  /* klee_trace_ret(); */
  /* klee_trace_param_i32((uint32_t)arr_out, "arr_out"); */
  if (!array_u16_cell_is_exposed)
    klee_allow_access(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE));
  klee_make_symbolic(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE),
                     "array_u16_model_cell");
  array_u16_index_allocated = 0;
  ARRAY_U16_EL_INIT(&array_u16_model_cell);
  array_u16_initialized = arr_out;
  klee_forbid_access(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE),
                     "array u16 private state");
  array_u16_cell_is_exposed = 0;
}

void array_u16_reset(struct ArrayU16 *arr)
{
  // No need for tracing, this is a shadow control function.
  klee_assert(!array_u16_cell_is_exposed);
  klee_allow_access(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE));
  klee_make_symbolic(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE),
                     "array_u16_model_cell");
  array_u16_index_allocated = 0;
  ARRAY_U16_EL_INIT(&array_u16_model_cell);
  array_u16_initialized = arr;
  klee_forbid_access(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE),
                     "array u16 private state");
  array_u16_cell_is_exposed = 0;
}

ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_U16_EL_TYPE));
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayU16), "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_u16_initialized);
  if (array_u16_index_allocated) {
    klee_assert(index == array_u16_allocated_index);
  } else {
    array_u16_allocated_index = index;
    array_u16_index_allocated = 1;
  }
  klee_allow_access(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE));
  array_u16_cell_is_exposed = 1;
  return &array_u16_model_cell;
}

void array_u16_end_access(struct ArrayU16 *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayU16), "arr");
  klee_assert(array_u16_index_allocated);
  klee_assert(arr == array_u16_initialized);
  klee_trace_extra_ptr(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE),
                       "returned_u16_cell");
  klee_forbid_access(&array_u16_model_cell, sizeof(ARRAY_U16_EL_TYPE),
                     "array u16 private state");
  array_u16_cell_is_exposed = 0;
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

void array_u16_init(struct ArrayU16 *arr_out)
{
  int i;
  for (i = 0; i < ARRAY_U16_CAPACITY; ++i) {
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
