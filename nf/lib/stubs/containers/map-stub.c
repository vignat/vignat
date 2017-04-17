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
  struct str_field_descr key_fields[PREALLOC_SIZE];
  // TODO: add descriptors for keys.
  map_keys_equality* keq;
};

int map_allocate(map_keys_equality* keq, smap_key_hash* khash,
                 int capacity,
                 struct Map** map_out) {
  klee_trace_ret();
  klee_trace_param_fptr(keq, "keq");
  klee_trace_param_fptr(khash, "khash");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_ptr(map_out, sizeof(struct Map*), "map_out");
  //int allocation_succeeded = klee_int("map_allocation_succeeded");
  *map_out = malloc(sizeof(struct Map));
  if (*map_out != NULL) { //(allocation_succeeded) {
    //TODO: can malloc return NULL during klee execution?
    klee_make_symbolic(*map_out, sizeof(struct Map), "map");
    klee_assert(map_out != NULL);
    (*map_out)->entry_claimed = 0;
    (*map_out)->keq = keq;
    (*map_out)->capacity = capacity;
    (*map_out)->has_layout = 0;
    klee_assume(0 <= (*map_out)->allocated_index);
    klee_assume((*map_out)->allocated_index < capacity);
    return 1;
  }
  return 0;
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
                    int key_fields_count) {
  klee_assert(key_fields_count < PREALLOC_SIZE);
  memcpy(map->key_fields, key_fields,
         sizeof(struct str_field_descr)*key_fields_count);
  map->key_field_count = key_fields_count;
  map->key_size = calculate_str_size(key_fields,
                                     key_fields_count);
  map->has_layout = 1;
}

int map_get(struct Map* map, void* key, int* value_out) {
  klee_trace_ret();
  klee_assert(map->has_layout);
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_ptr(key, map->key_size, "key");
  klee_trace_param_ptr(value_out, sizeof(int), "value_out");
  {
    for (int i = 0; i < map->key_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 map->key_fields[i].offset,
                                 map->key_fields[i].width,
                                 map->key_fields[i].name);
    }
  }
  if (map->has_this_key) {
    klee_assert(!map->entry_claimed);
    map->entry_claimed = 1;
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
  klee_trace_param_ptr(key, map->key_size, "key");
  klee_trace_param_i32(value, "value");
  {
    for (int i = 0; i < map->key_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 map->key_fields[i].offset,
                                 map->key_fields[i].width,
                                 map->key_fields[i].name);
    }
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
  klee_trace_param_ptr(key, map->key_size, "key");
  {
    for (int i = 0; i < map->key_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 map->key_fields[i].offset,
                                 map->key_fields[i].width,
                                 map->key_fields[i].name);
    }
  }
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
