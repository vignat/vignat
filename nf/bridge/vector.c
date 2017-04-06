#include <stdlib.h>
#include <stdint.h>
#include "vector.h"

struct Vector {
  uint8_t* data;
  int elem_size;
  int capacity;
};


int vector_allocate(int elem_size, int capacity,
                    struct Vector** vector_out) {
  struct Vector* old_vector_val = *vector_out;
  struct Vector* vector_alloc = malloc(sizeof(struct Vector));
  if (vector_alloc == NULL) return 0;
  *vector_out = (struct Vector*) vector_alloc;
  uint8_t* data_alloc = malloc(elem_size*capacity);
  if (data_alloc == NULL) {
    free(vector_alloc);
    *vector_out = old_vector_val;
    return 0;
  }
  (*vector_out)->elem_size = elem_size;
  (*vector_out)->capacity = capacity;
  return 1;
}

void* vector_borrow(struct Vector* vector, int index) {
  return vector->data + index*vector->elem_size;
}

void vector_return(struct Vector* vector, int index, void* value) {
  /* do nothing */
}
