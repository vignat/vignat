#include "array-bat.h"

// In-place initialization
void array_bat_init(struct ArrayBat *arr_out);
//@ requires true;
/* @ requires arr_out->data |-> ?data &*&
             chars(data, ARRAY_BAT_CAPACITY*sizeof(ARRAY_BAT_EL_TYPE), _); @*/
//@ ensures arrp_bat(_, arr_out);

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index);
//@ requires arrp_bat(?lst, arr) &*& 0 <= index &*& index < ARRAY_BAT_CAPACITY;
/*@ ensures arrp_bat_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_bat(arr, index) &*&
            batcherp(nth(index, lst), result); @*/

void array_bat_end_access(struct ArrayBat *arr);
/*@ requires arrp_bat_acc(?lst, arr, ?index) &*&
             batcherp(?x, arrp_the_missing_cell_bat(arr, index)); @*/
//@ ensures arrp_bat(update(index, x, lst), arr);


#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY_BAT_EL_TYPE array_bat_model_cell;
int array_bat_allocated_index;
int array_bat_index_allocated;
struct ArrayBat *array_bat_initialized;
int array_bat_cell_is_exposed = 1;

void array_bat_init(struct ArrayBat *arr_out)
{
  //No need to trace, since it is called from inside the
  // array2_init, which is traced. the spec for array2_init will
  // provide the necessary predicates, whilst array_bat_init is called
  // in the formally verified domain.

  if (!array_bat_cell_is_exposed)
    klee_allow_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE));
  klee_make_symbolic(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array_bat_model_cell");
  array_bat_index_allocated = 0;
  ARRAY_BAT_EL_INIT(&array_bat_model_cell);
  array_bat_initialized = arr_out;
  klee_forbid_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array bat private state");
  array_bat_cell_is_exposed = 0;
}

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_BAT_EL_TYPE));
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayBat), "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_bat_initialized);
  if (array_bat_index_allocated) {
    klee_assert(index == array_bat_allocated_index);
  } else {
    array_bat_allocated_index = index;
    array_bat_index_allocated = 1;
  }
  klee_allow_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE));
  array_bat_cell_is_exposed = 1;
  return &array_bat_model_cell;
}

void array_bat_end_access(struct ArrayBat *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayBat), "arr");
  klee_assert(array_bat_index_allocated);
  klee_assert(arr == array_bat_initialized);

  klee_forbid_access(&array_bat_model_cell, sizeof(ARRAY_BAT_EL_TYPE),
                     "array bat private state");
  array_bat_cell_is_exposed = 0;
  //nothing
}

#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_

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
