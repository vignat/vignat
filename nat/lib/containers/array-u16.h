#ifndef _ARRAY_U16_H_INCLUDED_
#define _ARRAY_U16_H_INCLUDED_

#include <stdint.h>
#include "../static-component-params.h"

#define ARRAY_U16_EL_TYPE uint16_t
#define ARRAY_U16_CAPACITY RTE_MAX_ETHPORTS
#define ARRAY_U16_EL_INIT (void)

#ifdef KLEE_VERIFICATION
struct ArrayU16
{
  char dummy;
};
#else//KLEE_VERIFICATION
struct ArrayU16
{
  ARRAY_U16_EL_TYPE data[ARRAY_U16_CAPACITY];
};
#endif//KLEE_VERIFICATION

/*@
  predicate some_u16p(uint16_t *p) = u_short_integer(p, _);
  @*/

/*@
  predicate arrp_u16(list<uint16_t> data, struct ArrayU16 *arr);
  predicate arrp_u16_acc(list<uint16_t> data, struct ArrayU16 *arr, int idx);

  fixpoint ARRAY_U16_EL_TYPE *arrp_the_missing_cell_u16(struct ArrayU16 *arr,
                                                        int idx) {
    return (unsigned short*)(arr->data)+idx;
  }
  @*/

// In-place initialization
void array_u16_init(struct ArrayU16 *arr_out);
/*@ requires ushorts((void*)(arr_out),
                     ARRAY_U16_CAPACITY, _) &*&
             struct_ArrayU16_padding(arr_out); @*/
//@ ensures arrp_u16(_, arr_out);

ARRAY_U16_EL_TYPE *array_u16_begin_access(struct ArrayU16 *arr, int index);
//@ requires arrp_u16(?lst, arr) &*& 0 <= index &*& index < ARRAY_U16_CAPACITY;
/*@ ensures arrp_u16_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_u16(arr, index) &*&
            u_short_integer(result, nth(index, lst)); @*/
void array_u16_end_access(struct ArrayU16 *arr);
/*@ requires arrp_u16_acc(?lst, arr, ?idx) &*&
             u_short_integer(arrp_the_missing_cell_u16(arr, idx), ?u16); @*/
//@ ensures arrp_u16(update(idx, u16, lst), arr);


#endif//_ARRAY_U16_H_INCLUDED_
