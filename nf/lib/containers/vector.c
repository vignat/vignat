#include <stdlib.h>
#include <stdint.h>
#include "vector.h"

struct Vector {
  uint8_t* data;
  int elem_size;
  int capacity;
};


int vector_allocate/*@ <t> @*/(int elem_size, int capacity,
                               vector_init_elem* init_elem,
                               struct Vector** vector_out)
/*@ requires 0 < elem_size &*& 0 < capacity &*&
             [_]is_vector_init_elem(init_elem, ?entp) &*&
             *vector_out |-> ?old_vo; @*/
/*@ ensures result == 0 ?
              (*vector_out |-> old_vo) :
              (*vector_out |-> ?new_vo &*&
               vectorp(new_vo, entp, _)); @*/
{
  struct Vector* old_vector_val = *vector_out;
  struct Vector* vector_alloc = malloc(sizeof(struct Vector));
  if (vector_alloc == 0) return 0;
  *vector_out = (struct Vector*) vector_alloc;
  uint8_t* data_alloc = malloc(elem_size*capacity);
  if (data_alloc == 0) {
    free(vector_alloc);
    *vector_out = old_vector_val;
    return 0;
  }
  (*vector_out)->data = data_alloc;
  (*vector_out)->elem_size = elem_size;
  (*vector_out)->capacity = capacity;
  for (int i = 0; i < capacity; ++i) {
    init_elem((*vector_out)->data + elem_size*i);
  }
  return 1;
}

void* vector_borrow/*@ <t> @*/(struct Vector* vector, int index)
/*@ requires vectorp(vector, ?entp, ?values) &*&
             0 <= index &*& index < length(values); @*/
/*@ ensures vector_accp(vector, entp, values, index, result) &*&
            entp(result, nth(index, values)); @*/
{
  return vector->data + index*vector->elem_size;
}

void vector_return/*@ <t> @*/(struct Vector* vector, int index, void* value)
/*@ requires vector_accp(vector, ?entp, ?values, index, value) &*&
             entp(value, ?v); @*/
/*@ ensures vectorp(vector, entp, update(index, v, values)); @*/
{
  /* do nothing */
}
