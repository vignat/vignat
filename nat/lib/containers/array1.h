#ifndef _ARRAY1_H_INCLUDED_
#define _ARRAY1_H_INCLUDED_

#ifndef ARRAY1_EL_TYPE
#  error "Must define the array1 element type."
#endif//ARRAY1_EL_TYPE

#ifndef ARRAY1_CAPACITY
#  error "Must define the array1 capacity."
#endif//ARRAY1_CAPACITY

struct Array1
{
  ARRAY1_EL_TYPE data[ARRAY1_CAPACITY];
};

// In-place initialization
void array1_init(struct Array1 *arr_out);
ARRAY1_EL_TYPE *array1_begin_access(struct Array1 *arr, int index);
void array1_end_access(struct Array1 *arr, int index);


void array1_init(struct Array1 *arr_out)
{
  (void)arr_out;
  //nothing
}

ARRAY1_EL_TYPE *array1_begin_access(struct Array1 *arr, int index)
{
  return arr->data + index;
}

void array1_end_access(struct Array1 *arr, int index)
{
  (void)arr;
  (void)index;
  //nothing
}

#endif//_ARRAY1_H_INCLUDED_
