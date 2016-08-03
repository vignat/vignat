#ifndef _ARRAY1_H_INCLUDED_
#define _ARRAY1_H_INCLUDED_

#ifndef ARRAY1_EL_TYPE
#  error "Must define the array1 element type."
#endif//ARRAY1_EL_TYPE

#ifndef ARRAY1_CAPACITY
#  error "Must define the array1 capacity."
#endif//ARRAY1_CAPACITY

#ifndef ARRAY1_EL_INIT
#  error "Must define the array1 element initializer function."
#endif//ARRAY1_EL_INIT

struct Array1
{
  ARRAY1_EL_TYPE data[ARRAY1_CAPACITY];
};

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
  (void)index;
  //nothing
}

#endif//_ARRAY1_H_INCLUDED_
