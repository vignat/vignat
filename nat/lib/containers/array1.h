#ifndef _ARRAY1_H_INCLUDED_
#define _ARRAY1_H_INCLUDED_

#ifndef ARRAY1_EL_TYPE
#  error "Must define the array1 element type."
#endif//ARRAY1_EL_TYPE

#ifndef ARRAY1_CAPACITY
#  error "Must define the array1 capacity."
#endif//ARRAY1_CAPACITY

// ARRAY1_EL_INIT must have the contract converting char[] to
// ARRAY1_EL_TYPE
#ifndef ARRAY1_EL_INIT
#  error "Must define the array1 element initializer function."
#endif//ARRAY1_EL_INIT

struct Array1;

/*@
  //params: T1, P1
  predicate arrp1(list<T1> data, struct Array1* arr);
  predicate arrp1_acc(listT1> data, struct Array1* arr,
                      int idx, ARRAY1_EL_TYPE *el);
  @*/

// In-place initialization
void array1_init(struct Array1 *arr_out);
/*@ requires arr_out->data |-> ?data &*&
             chars(data, ARRAY1_CAPACITY*sizeof(ARRAY1_EL_TYPE), _); @*/
//@ ensures arrp1(_, arr_out);

ARRAY1_EL_TYPE *array1_begin_access(struct Array1 *arr, int index);
//@ requires arrp1(lst, arr) &*& 0 <= index &*& index < ARRAY1_CAPACITY;
/*@ ensures arrp1_acc(lst, arr, index, result) &*&
            P1(result, nth(lst, index)); @*/

void array1_end_access(struct Array1 *arr);
/*@ requites arrp1_acc(lst, arr, ?index, ?ptr) &*&
             P1(ptr, ?x); @*/
//@ ensures arrp1(update(index, x, lst), arr);


#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct Array1
{
  char dummy;
};

ARRAY1_EL_TYPE array1_model_cell;
int array1_allocated_index;
int array1_index_allocated;
struct Array1 *array1_initialized;

void array1_init(struct Array1 *arr_out)
{
  //No need to trace, since it is called from inside the
  // array2_init, which is traced. the spec for array2_init will
  // provide the necessary predicates, whilst array1_init is called
  // in the formally verified domain.
  //klee_trace_ret();
  //klee_trace_param_i32((uint32_t)arr_out, "arr_out");

  klee_make_symbolic(&array1_model_cell, sizeof(ARRAY1_EL_TYPE),
                     "array1_model_cell");
  array1_index_allocated = 0;
  ARRAY1_EL_INIT(&array1_model_cell);
  array1_initialized = arr_out;
}

ARRAY1_EL_TYPE *array1_begin_access(struct Array1 *arr, int index)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array1_initialized);
  if (array1_index_allocated) {
    klee_assert(index == array1_allocated_index);
  } else {
    array1_allocated_index = index;
    array1_index_allocated = 1;
  }
  return &array1_model_cell;
}

void array1_end_access(struct Array1 *arr)
{
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)arr, "arr");
  klee_assert(array1_index_allocated);
  klee_assert(arr == array1_initialized);
  //nothing
}

#else//KLEE_VERIFICATION

struct Array1
{
  ARRAY1_EL_TYPE data[ARRAY1_CAPACITY];
};

void array1_init(struct Array1 *arr_out)
{
  for (int i = 0; i < ARRAY1_CAPACITY; ++i) {
    ARRAY1_EL_INIT(arr_out->data[i]);
  }
}

ARRAY1_EL_TYPE *array1_begin_access(struct Array1 *arr, int index)
{
  return arr->data + index;
}

void array1_end_access(struct Array1 *arr)
{
  (void)arr;
  //nothing
}

#endif//KLEE_VERIFICATION

#endif//_ARRAY1_H_INCLUDED_
