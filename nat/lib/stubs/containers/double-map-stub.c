#include <string.h>
#include <assert.h>
#include "klee/klee.h"
#include "lib/containers/double-map.h"
#include "double-map-stub-control.h"

#define prealloc_size (256)

int key_a_size_g = 0;
int key_a_offset_g = 0;
int key_b_size_g = 0;
int key_b_offset_g = 0;
int value_size_g = 0;

//uint8_t key_a[prealloc_size];
//uint8_t key_b[prealloc_size]; //no need for separate key storage
uint8_t value[prealloc_size];
int allocation_succeeded;
int has_this_key;
int entry_claimed = 0;
int allocated_index;
struct DoubleMap* allocated_map_ptr;

entry_condition* ent_cond = NULL;
struct str_field_descr key_a_fields[prealloc_size],
  key_b_fields[prealloc_size],
  value_fields[prealloc_size];
int key_a_field_count = 0,
  key_b_field_count = 0,
  value_field_count = 0;

void dmap_set_entry_condition(entry_condition* c) {
  klee_trace_param_fptr(c, "c");
  ent_cond = c;
}

void dmap_set_layout(struct str_field_descr* key_a_field_, int key_a_count_,
                     struct str_field_descr* key_b_field_, int key_b_count_,
                     struct str_field_descr* value_field_, int value_count_) {
  klee_assert(key_a_count_ < prealloc_size);
  klee_assert(key_b_count_ < prealloc_size);
  klee_assert(value_count_ < prealloc_size);
  memcpy(key_a_fields, key_a_field_, sizeof(struct str_field_descr)*key_a_count_);
  memcpy(key_b_fields, key_b_field_, sizeof(struct str_field_descr)*key_b_count_);
  memcpy(value_fields, value_field_, sizeof(struct str_field_descr)*value_count_);
  key_a_field_count = key_a_count_;
  key_b_field_count = key_b_count_;
  value_field_count = value_count_;
}

int dmap_allocate(int key_a_size,
                  int key_a_offset,
                  map_keys_equality eq_a,
                  int key_b_size,
                  int key_b_offset,
                  map_keys_equality eq_b,
                  int value_size,
                  int capacity,
                  struct DoubleMap** map_out) {
  klee_trace_ret();
  klee_trace_param_i32(key_a_size, "key_a_size");
  klee_trace_param_i32(key_a_offset, "key_a_offset");
  klee_trace_param_fptr(eq_a, "eq_a");
  klee_trace_param_i32(key_b_size, "key_b_size");
  klee_trace_param_i32(key_b_offset, "key_b_offset");
  klee_trace_param_fptr(eq_b, "eq_b");
  klee_trace_param_i32(value_size, "value_size");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_ptr(map_out, sizeof(struct DoubleMap*), "map_out");

  allocation_succeeded = klee_int("dmap_allocation_succeeded");
  if (allocation_succeeded) {
    klee_make_symbolic(&allocated_map_ptr, sizeof(struct DoubleMap*),
                       "allocated_map_do_not_dereference");
    *map_out = allocated_map_ptr;

    klee_assert(key_a_size < prealloc_size);
    klee_assert(key_b_size < prealloc_size);
    klee_assert(value_size < prealloc_size);
    klee_assert(key_a_offset + key_a_size < value_size);
    klee_assert(key_b_offset + key_b_size < value_size);

    //No need to allocate keys separately, since we know that
    //the keys are stored in the value
    //-klee_make_symbolic(key_a, prealloc_size, "dmap_key_a");
    //-klee_make_symbolic(key_b, prealloc_size, "dmap_key_b");
    klee_make_symbolic(value, prealloc_size, "dmap_value");

    has_this_key = klee_int("dmap_has_this_key");
    entry_claimed = 0;
    allocated_index = klee_int("dmap_allocated_index");

    klee_assume(0 <= allocated_index);
    klee_assume(allocated_index < capacity);

    key_a_size_g = key_a_size;
    key_a_offset_g = key_a_offset;
    key_b_size_g = key_b_size;
    key_b_offset_g = key_b_offset;
    value_size_g = value_size;
    // Do not assume the ent_cond here, because depending on what comes next,
    // we may change the key_a, key_b or value. we assume the condition after
    // that change.
    return 1;
  }
  return 0;
}

int dmap_get_a(struct DoubleMap* map, void* key, int* index) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_ptr(key, key_a_size_g, "key");
  klee_trace_param_ptr(index, sizeof(int), "index");
  {
    for (int i = 0; i < key_a_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 key_a_fields[i].offset,
                                 key_a_fields[i].width,
                                 key_a_fields[i].name);
    }
  }
  klee_assert(allocation_succeeded);
  klee_assert(map == allocated_map_ptr);
  if (has_this_key) {
    klee_assert(!entry_claimed);
    memcpy(value + key_a_offset_g, key, key_a_size_g);
    if (ent_cond)
      klee_assume(ent_cond(value + key_a_offset_g,
                           value + key_b_offset_g,
                           allocated_index, value));
    entry_claimed = 1;
    *index = allocated_index;
    return 1;
  }
  return 0;
}

int dmap_get_b(struct DoubleMap* map, void* key, int* index) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_ptr(key, key_b_size_g, "key");
  klee_trace_param_ptr(index, sizeof(int), "index");
  {
    for (int i = 0; i < key_b_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 key_b_fields[i].offset,
                                 key_b_fields[i].width,
                                 key_b_fields[i].name);
    }
  }
  klee_assert(allocation_succeeded);
  klee_assert(map == allocated_map_ptr);
  if (has_this_key) {
    klee_assert(!entry_claimed);
    memcpy(value + key_b_offset_g, key, key_b_size_g);
    if (ent_cond) klee_assume(ent_cond(value + key_a_offset_g,
                                       value + key_b_offset_g,
                                       allocated_index, value));
    entry_claimed = 1;
    *index = allocated_index;
    return 1;
  }
  return 0;
}

int dmap_put(struct DoubleMap* map, void* value_, int index) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_ptr(value_, value_size_g, "value_");
  klee_trace_param_i32(index, "index");
  {
    for (int i = 0; i < value_field_count; ++i) {
      klee_trace_param_ptr_field(value_,
                                 value_fields[i].offset,
                                 value_fields[i].width,
                                 value_fields[i].name);
    }
  }
  // Can not ever fail, because index is guaranteed to point to the available
  // slot, therefore the map can not be full at this point.
  // Always returns 1.
  klee_assert(allocation_succeeded);
  klee_assert(map == allocated_map_ptr);
  if (entry_claimed) {
    klee_assert(allocated_index == index);
  }
  memcpy(value, value_, value_size_g);
  // This must be provided by the caller, since it his responsibility
  // to fulfill the value by the same index:
  klee_assert(ent_cond == NULL || ent_cond(value + key_a_offset_g,
                                           value + key_b_offset_g,
                                           index,
                                           value));
  entry_claimed = 1;
  allocated_index = index;
  return 1;
}

int dmap_erase(struct DoubleMap* map, int index) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_i32(index, "index");

  klee_assert(allocation_succeeded);
  klee_assert(map == allocated_map_ptr);
  klee_assert(0); //This model does not support erasure.
  return 0;
}

void dmap_get_value(struct DoubleMap* map, int index, void* value_out) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_i32(index, "index");
  klee_trace_param_ptr(value_out, value_size_g, "value_out");
  {
    for (int i = 0; i < value_field_count; ++i) {
      klee_trace_param_ptr_field(value_out,
                                 value_fields[i].offset,
                                 value_fields[i].width,
                                 value_fields[i].name);
    }
  }
  klee_assert(allocation_succeeded);
  klee_assert(map == allocated_map_ptr);
  if (entry_claimed) {
    klee_assert(index == allocated_index);
  } else {
    allocated_index = index;
    entry_claimed = 1;
  }
  memcpy(value_out, value, value_size_g);
}

int dmap_size(struct DoubleMap* map) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_assert(0); //This model does not support size requests.
  return -1;
}
