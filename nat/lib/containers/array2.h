#ifndef _ARRAY2_H_INCLUDED_
#define _ARRAY2_H_INCLUDED_

#ifndef ARRAY2_EL_TYPE
#  error "Must define the array2 element type."
#endif//ARRAY2_EL_TYPE

#ifndef ARRAY2_CAPACITY
#  error "Must define the array2 capacity."
#endif//ARRAY2_CAPACITY

struct Array2
{
  ARRAY2_EL_TYPE data[ARRAY2_CAPACITY];
};

// In-place initialization
void array2_init(struct Array2 *arr_out);
ARRAY2_EL_TYPE *array2_begin_access(struct Array2 *arr, int index);
void array2_end_access(struct Array2 *arr);


void array2_init(struct Array2 *arr_out)
{
  for (int i = 0; i < ARRAY2_CAPACITY; ++i) {
    ARRAY2_EL_INIT(arr_out->data[i]);
  }
}

ARRAY2_EL_TYPE *array2_begin_access(struct Array2 *arr, int index)
{
  return arr->data + index;
}

void array2_end_access(struct Array2 *arr)
{
  (void)arr;
  (void)index;
  //nothing
}

#endif//_ARRAY2_H_INCLUDED_
