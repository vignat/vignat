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
  struct nested_field_descr nest_fields[PREALLOC_SIZE];
  int field_count;
  int nested_field_count;
  char* cell_type;
};

int vector_allocate(int elem_size, int capacity,
                    vector_init_elem* init_elem,
                    struct Vector** vector_out) {
  klee_trace_ret();
  klee_trace_param_i32(elem_size, "elem_size");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_fptr(init_elem, "init_elem");
  klee_trace_param_ptr(vector_out, sizeof(struct Vector*), "vector_out");

  int allocation_succeeded = klee_int("vector_alloc_success");
  if (! allocation_succeeded) return 0;

  *vector_out = malloc(sizeof(struct Vector));
  klee_assume(*vector_out != NULL);
  klee_make_symbolic(*vector_out, sizeof(struct Vector), "vector");
  (*vector_out)->data = malloc(elem_size);
  klee_assume((*vector_out)->data != NULL);
  klee_make_symbolic((*vector_out)->data, elem_size, "vector_data");
  (*vector_out)->elem_size = elem_size;
  (*vector_out)->capacity = capacity;
  (*vector_out)->elem_claimed = 0;
  (*vector_out)->field_count = 0;
  (*vector_out)->nested_field_count = 0;
  klee_forbid_access((*vector_out)->data, elem_size, "private state");
  return 1;
}

void vector_reset(struct Vector* vector) {
  //Do not trace. This function is an internal knob of the model.
  //TODO: reallocate vector->data to avoid having the same pointer?
  klee_allow_access(vector->data, vector->elem_size);
  klee_make_symbolic(vector->data, vector->elem_size, "vector_data_reset");
  vector->elem_claimed = 0;
  klee_forbid_access(vector->data, vector->elem_size, "private state");
}

void vector_set_layout(struct Vector* vector,
                       struct str_field_descr* value_fields,
                       int field_count,
                       struct nested_field_descr* val_nest_fields,
                       int nest_field_count,
                       char* type_tag) {
  //Do not trace. This function is an internal knob of the model.
  klee_assert(field_count < PREALLOC_SIZE);
  memcpy(vector->fields, value_fields,
         sizeof(struct str_field_descr)*field_count);
  vector->field_count = field_count;

  if (0 < nest_field_count) {
    klee_assert(nest_field_count < PREALLOC_SIZE);
    memcpy(vector->nest_fields, val_nest_fields,
           sizeof(struct nested_field_descr)*nest_field_count);
  }
  vector->nested_field_count = nest_field_count;
  vector->cell_type = type_tag;
}

void vector_borrow(struct Vector* vector, int index, void** val_out) {
  klee_trace_ret();
  //Avoid dumpting the actual contents of vector.
  klee_trace_param_i32((uint32_t)vector, "vector");
  klee_trace_param_i32(index, "index");
  klee_trace_param_ptr(val_out, sizeof(void*), "val_out");
  klee_trace_extra_ptr(vector->data, vector->elem_size,
                       "borrowed_cell", vector->cell_type);
  {
    for (int i = 0; i < vector->field_count; ++i) {
      klee_trace_extra_ptr_field(vector->data,
                                 vector->fields[i].offset,
                                 vector->fields[i].width,
                                 vector->fields[i].name);
    }
    for (int i = 0; i < vector->nested_field_count; ++i) {
      klee_trace_extra_ptr_nested_field(vector->data,
                                        vector->nest_fields[i].base_offset,
                                        vector->nest_fields[i].offset,
                                        vector->nest_fields[i].width,
                                        vector->nest_fields[i].name);
    }
  }
  klee_assert(!vector->elem_claimed);
  vector->elem_claimed = 1;
  vector->index_claimed = index;
  klee_allow_access(vector->data, vector->elem_size);
  *val_out = vector->data;
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
    for (int i = 0; i < vector->nested_field_count; ++i) {
      klee_trace_param_ptr_nested_field(vector->data,
                                        vector->nest_fields[i].base_offset,
                                        vector->nest_fields[i].offset,
                                        vector->nest_fields[i].width,
                                        vector->nest_fields[i].name);
    }
  }
  klee_assert(vector->elem_claimed);
  klee_assert(vector->index_claimed == index);
  klee_assert(vector->data == value);
  klee_forbid_access(vector->data, vector->elem_size, "private state");
}
