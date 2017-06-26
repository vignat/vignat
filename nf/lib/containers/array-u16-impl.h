#include "array-u16.h"
#include "../ignore.h"

//@ #include "arith.gh"
//@ #include "stdex.gh"

/*@
  predicate arrp_u16(list<uint16_t> data, struct ArrayU16 *arr) =
    struct_ArrayU16_padding(arr) &*&
    true == ((char*)0 <= (void*)arr->data) &*&
    true == ((void*)((unsigned short*)arr->data + ARRAY_U16_CAPACITY) <=
             (char*)UINTPTR_MAX) &*&
    ushorts(arr->data, ARRAY_U16_CAPACITY, data);

  predicate arrp_u16_acc(list<uint16_t> data, struct ArrayU16 *arr, int idx) =
    0 <= idx &*& idx < ARRAY_U16_CAPACITY &*&
    struct_ArrayU16_padding(arr) &*&
    true == ((char*)0 <= (void*)arr->data) &*&
    true == ((void*)((unsigned short*)arr->data + ARRAY_U16_CAPACITY) <=
             (char*)UINTPTR_MAX) &*&
    length(data) == ARRAY_U16_CAPACITY &*&
    ushorts(arr->data, idx, take(idx, data)) &*&
    ushorts((unsigned short *)arr->data + idx + 1, ARRAY_U16_CAPACITY - idx - 1, drop(idx+1, data));


  @*/

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

/*@
  lemma void ushorts_limits(unsigned short* p)
  requires ushorts(p, ?len, ?lst) &*&
           p <= (unsigned short*)UINTPTR_MAX;
  ensures ushorts(p, len, lst) &*&
          true == (p + len <= (unsigned short*)UINTPTR_MAX);
  {
    open ushorts(p, len, lst);
    switch(lst) {
      case nil:
      case cons(h,t):
        u_short_integer_limits(p);
        ushorts_limits(p+1);
    }
    close ushorts(p, len, lst);
  }
  @*/
void array_u16_init(struct ArrayU16 *arr_out)
/*@ requires ushorts((void*)(arr_out),
                     ARRAY_U16_CAPACITY, _) &*&
             struct_ArrayU16_padding(arr_out); @*/
//@ ensures arrp_u16(_, arr_out);
{
  //@ ushorts_limits(arr_out->data);
  IGNORE(arr_out);
  //@ close arrp_u16(_, arr_out);
}

/*@
  lemma void extract_by_index(ARRAY_U16_EL_TYPE* arr, int idx)
  requires ushorts(arr, ?len, ?lst) &*& 0 <= idx &*& idx < len;
  ensures ushorts(arr, idx, take(idx, lst)) &*&
          u_short_integer(arr + idx, nth(idx, lst)) &*&
          ushorts(arr+idx+1, len - idx - 1, drop(idx+1,lst));
  {
    open ushorts(arr, len, lst);
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
          close ushorts(arr, 0, nil);
        } else {
          extract_by_index(arr+1, idx-1);
          close ushorts(arr, idx, take(idx, lst));
        }
    }
  }
  @*/
ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index)
//@ requires arrp_u16(?lst, arr) &*& 0 <= index &*& index < ARRAY_U16_CAPACITY;
/*@ ensures arrp_u16_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_u16(arr, index) &*&
            u_short_integer(result, nth(index, lst)); @*/
{
  //@ open arrp_u16(lst, arr);
  //@ extract_by_index(arr->data, index);
  //@ mul_mono_strict(index, ARRAY_U16_CAPACITY, sizeof(ARRAY_U16_EL_TYPE));
  return (unsigned short*)(arr->data) + index;
  //@ close arrp_u16_acc(lst, arr, index);
}

/*@
  lemma void glue_array(ARRAY_U16_EL_TYPE* arr, int idx,
                        list<int> lst)
  requires ushorts(arr, idx, take(idx, lst)) &*&
           u_short_integer(arr + idx, nth(idx, lst)) &*&
           ushorts(arr+idx+1, length(lst) - idx - 1,
                  drop(idx+1,lst)) &*&
           0 <= idx &*& idx < length(lst);
  ensures ushorts(arr, length(lst), lst);
  {
    open ushorts(arr, idx, take(idx, lst));
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
        } else {
          glue_array(arr+1, idx-1, t);
        }
    }
    close ushorts(arr, length(lst), lst);
  }
  @*/
void array_u16_end_access(struct ArrayU16 *arr)
/*@ requires arrp_u16_acc(?lst, arr, ?idx) &*&
             u_short_integer(arrp_the_missing_cell_u16(arr, idx), ?u16); @*/
//@ ensures arrp_u16(update(idx, u16, lst), arr);
{
  //@ open arrp_u16_acc(lst, arr, idx);
  //@ take_update_unrelevant(idx, idx, u16, lst);
  //@ nth_update(idx, idx, u16, lst);
  //@ drop_update_unrelevant(idx+1, idx, u16, lst);
  //@ glue_array(arr->data, idx, update(idx, u16, lst));
  IGNORE(arr);
  //@ close arrp_u16(update(idx, u16, lst), arr);
}

#endif//KLEE_VERIFICATION
