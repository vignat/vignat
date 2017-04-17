#include "klee/klee.h"
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "lib/containers/vector.h"
#include "vector-stub-control.h"

#define PREALLOC_SIZE (256)

struct Vector {
  uint8_t* data;
  int elem_size;
  int capacity;
  int elem_claimed;
  int index_claimed;
  struct str_field_descr fields[PREALLOC_SIZE];
  int field_count;
};

int vector_allocate(int elem_size, int capacity,
                    struct Vector** vector_out) {
  klee_trace_ret();
  klee_trace_param_i32(elem_size, "elem_size");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_ptr(vector_out, sizeof(struct Vector*), "vector_out");

  /* int allocation_succeeded = klee_int("vector_alloc_success"); */
  /* if (! allocation_succeeded) return 0; */

  *vector_out = malloc(sizeof(struct Vector));
  if (*vector_out == NULL) return 0;
  klee_make_symbolic(*vector_out, sizeof(struct Vector), "vector");
  (*vector_out)->data = malloc(elem_size);
  if ((*vector_out)->data == NULL) return 0;
  klee_make_symbolic((*vector_out)->data, elem_size, "vector_data");
  (*vector_out)->elem_size = elem_size;
  (*vector_out)->capacity = capacity;
  (*vector_out)->elem_claimed = 0;
  return 1;
}

void vector_reset(struct Vector* vector) {
  //Do not trace. This function is an internal knob of the model.
  //TODO: reallocate vector->data to avoid having the same pointer?
  klee_make_symbolic(vector->data, vector->elem_size, "vector_data_reset");
  vector->elem_claimed = 0;
}

void vector_set_layout(struct Vector* vector,
                       struct str_field_descr* value_fields,
                       int field_count) {
  //Do not trace. This function is an internal knob of the model.
  klee_assert(field_count < PREALLOC_SIZE);
  memcpy(vector->fields, value_fields,
         sizeof(struct str_field_descr)*field_count);
  vector->field_count = field_count;
}

void* vector_borrow(struct Vector* vector, int index) {
  klee_trace_ret();
  //Avoid dumpting the actual contents of vector.
  klee_trace_param_i32((uint32_t)vector, "vector");
  klee_trace_param_i32(index, "index");
  klee_assert(!vector->elem_claimed);
  vector->elem_claimed = 1;
  vector->index_claimed = index;
  return vector->data;
}

void vector_return(struct Vector* vector, int index, void* value) {
  klee_trace_ret();
  //Avoid dumpting the actual contents of vector.
  klee_trace_param_i32((uint32_t)vector, "vector");
  klee_trace_param_i32(index, "index");
  klee_trace_param_ptr(value, vector->elem_size, "value");
  {
    for (int i = 0; i < vector->field_count; ++i) {
      klee_trace_param_ptr_field(value,
                                 vector->fields[i].offset,
                                 vector->fields[i].width,
                                 vector->fields[i].name);
    }
  }
  klee_assert(vector->elem_claimed);
  klee_assert(vector->index_claimed == index);
  klee_assert(vector->data == value);
}
