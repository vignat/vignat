#include <stdlib.h>
#include <string.h>
#include "klee/klee.h"
#include "lib/containers/map.h"
#include "map-stub-control.h"

#define PREALLOC_SIZE (256)

struct Map {
  void* keyp;
  int has_this_key;
  int entry_claimed;
  int allocated_index;
  int capacity;

  int has_layout;
  int key_size;
  int key_field_count;
  int nested_key_field_count;
  map_entry_condition* ent_cond;
  struct str_field_descr key_fields[PREALLOC_SIZE];
  struct nested_field_descr key_nests[PREALLOC_SIZE];
  char* key_type;
  map_keys_equality* keq;
};

int map_allocate(map_keys_equality* keq, map_key_hash* khash,
                 int capacity,
                 struct Map** map_out) {
  klee_trace_ret();
  klee_trace_param_fptr(keq, "keq");
  klee_trace_param_fptr(khash, "khash");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_ptr(map_out, sizeof(struct Map*), "map_out");
  int allocation_succeeded = klee_int("map_allocation_succeeded");
  if (allocation_succeeded) {
    *map_out = malloc(sizeof(struct Map));
    klee_assume(*map_out != NULL);
    klee_make_symbolic((*map_out), sizeof(struct Map), "map");
    klee_assert((*map_out) != NULL);
    (*map_out)->entry_claimed = 0;
    (*map_out)->keq = keq;
    (*map_out)->capacity = capacity;
    (*map_out)->has_layout = 0;
    (*map_out)->ent_cond = 0;
    return 1;
  }
  return 0;
}

void map_reset(struct Map* map) {
  //Do not trace. This function is an internal knob of the model.
  map->keyp = NULL;
  map->entry_claimed = 0;
  map->has_this_key = klee_int("map_has_this_key");
  map->allocated_index = klee_int("map_allocated_index");
}

static
int calculate_str_size(struct str_field_descr* descr, int len) {
  int rez = 0;
  int sum = 0;
  for (int i = 0; i < len; ++i) {
    sum += descr[i].width;
    if (descr[i].offset + descr[i].width > rez)
      rez = descr[i].offset + descr[i].width;
  }
  klee_assert(rez == sum);
  return rez;
}

void map_set_layout(struct Map* map,
                    struct str_field_descr* key_fields,
                    int key_fields_count,
                    struct nested_field_descr* key_nests,
                    int nested_key_fields_count,
                    char* key_type) {
  //Do not trace. This function is an internal knob of the model.
  klee_assert(key_fields_count < PREALLOC_SIZE);
  klee_assert(nested_key_fields_count < PREALLOC_SIZE);
  memcpy(map->key_fields, key_fields,
         sizeof(struct str_field_descr)*key_fields_count);
  if (0 < nested_key_fields_count) {
    memcpy(map->key_nests, key_nests,
           sizeof(struct nested_field_descr)*nested_key_fields_count);
  }
  map->key_field_count = key_fields_count;
  map->nested_key_field_count = nested_key_fields_count;
  map->key_size = calculate_str_size(key_fields,
                                     key_fields_count);
  map->has_layout = 1;
  map->key_type = key_type;
}

void map_set_entry_condition(struct Map* map, map_entry_condition* cond) {
  map->ent_cond = cond;
}


#define TRACE_KEY_FIELDS(key, map)                                      \
  {                                                                     \
    for (int i = 0; i < map->key_field_count; ++i) {                    \
      klee_trace_param_ptr_field(key,                                   \
                                 map->key_fields[i].offset,             \
                                 map->key_fields[i].width,              \
                                 map->key_fields[i].name);              \
    }                                                                   \
    for (int i = 0; i < map->nested_key_field_count; ++i) {            \
      klee_trace_param_ptr_nested_field(key,                            \
                                        map->key_nests[i].base_offset,  \
                                        map->key_nests[i].offset,       \
                                        map->key_nests[i].width,        \
                                        map->key_nests[i].name);        \
    }                                                                   \
  }

int map_get(struct Map* map, void* key, int* value_out) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_tagged_ptr(key, map->key_size, "key", map->key_type);
  klee_trace_param_ptr(value_out, sizeof(int), "value_out");
  TRACE_KEY_FIELDS(key, map);
  if (map->has_this_key) {
    klee_assert(!map->entry_claimed);
    map->entry_claimed = 1;
    if (map->ent_cond) {
      klee_assume(map->ent_cond(key, map->allocated_index));
    }
    *value_out = map->allocated_index;
    return 1;
  }
  return 0;
}

void map_put(struct Map* map, void* key, int value) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_tagged_ptr(key, map->key_size, "key", map->key_type);
  klee_trace_param_i32(value, "value");
  TRACE_KEY_FIELDS(key, map);
  if (map->ent_cond) {
    klee_assert(map->ent_cond(key, value));
  }
  if (map->entry_claimed) {
    klee_assert(map->allocated_index == value);
  }
  map->keyp = key;
  map->entry_claimed = 1;
  map->allocated_index = value;
}

void map_erase(struct Map* map, void* key, void** trash) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_tagged_ptr(key, map->key_size, "key", map->key_type);
  TRACE_KEY_FIELDS(key, map);
  klee_trace_param_ptr(trash, sizeof(void*), "trash");
  klee_assert(0); //no support for erasing staff for the moment
}

int map_size(struct Map* map) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_assert(0); //No support for retreiving size for now.
}
