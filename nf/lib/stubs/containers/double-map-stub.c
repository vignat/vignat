#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "klee/klee.h"
#include "lib/containers/double-map.h"
#include "double-map-stub-control.h"

#define prealloc_size (256)

#define ALLOW(map) klee_allow_access((map), sizeof(struct DoubleMap))
#define DENY(map) klee_forbid_access((map), sizeof(struct DoubleMap), "allocated_map_do_not_dereference")

struct DoubleMap {
  int key_a_size_g;
  int key_b_size_g;
  int value_size_g;
  uint8_t value[prealloc_size];
  int has_this_key;
  int entry_claimed;
  int allocated_index;

  entry_condition* ent_cond;
  struct str_field_descr key_a_fields[prealloc_size];
  struct str_field_descr key_b_fields[prealloc_size];
  struct str_field_descr value_fields[prealloc_size];
  struct nested_field_descr value_nests[prealloc_size];
  int key_a_field_count;
  int key_b_field_count;
  int value_field_count;
  int value_nests_count;

  map_keys_equality* eq_a_g;
  map_keys_equality* eq_b_g;
  dmap_extract_keys* dexk_g;
  dmap_pack_keys* dpk_g;
};

void dmap_set_entry_condition(struct DoubleMap* map, entry_condition* c) {
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_fptr(c, "c");
  ALLOW(map);
  map->ent_cond = c;
  DENY(map);
}

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

void dmap_set_layout(struct DoubleMap* map,
                     struct str_field_descr* key_a_field_, int key_a_count_,
                     struct str_field_descr* key_b_field_, int key_b_count_,
                     struct str_field_descr* value_field_, int value_count_,
                     struct nested_field_descr* value_nests_, int value_nests_count_) {
  ALLOW(map);
  klee_assert(key_a_count_ < prealloc_size);
  klee_assert(key_b_count_ < prealloc_size);
  klee_assert(value_count_ < prealloc_size);
  klee_assert(value_nests_count_ < prealloc_size);
  memcpy(map->key_a_fields, key_a_field_, sizeof(struct str_field_descr)*key_a_count_);
  memcpy(map->key_b_fields, key_b_field_, sizeof(struct str_field_descr)*key_b_count_);
  memcpy(map->value_fields, value_field_, sizeof(struct str_field_descr)*value_count_);
  memcpy(map->value_nests, value_nests_, sizeof(struct nested_field_descr)*value_nests_count_);
  map->key_a_field_count = key_a_count_;
  map->key_b_field_count = key_b_count_;
  map->value_field_count = value_count_;
  map->value_nests_count = value_nests_count_;
  map->key_a_size_g = calculate_str_size(key_a_field_, key_a_count_);
  map->key_b_size_g = calculate_str_size(key_b_field_, key_b_count_);
  DENY(map);
}

int dmap_allocate(map_keys_equality eq_a,
                  map_key_hash hsh_a,
                  map_keys_equality eq_b,
                  map_key_hash hsh_b,
                  int value_size,
                  uq_value_copy v_cpy,
                  uq_value_destr v_destr,
                  dmap_extract_keys dexk,
                  dmap_pack_keys dpk,
                  int capacity,
                  int keys_capacity,
                  struct DoubleMap** map_out) {
  klee_trace_ret();
  klee_trace_param_fptr(eq_a, "eq_a");
  klee_trace_param_fptr(hsh_a, "hsh_a");
  klee_trace_param_fptr(eq_b, "eq_b");
  klee_trace_param_fptr(hsh_b, "hsh_b");
  klee_trace_param_i32(value_size, "value_size");
  klee_trace_param_fptr(v_cpy, "v_cpy");
  klee_trace_param_fptr(v_destr, "v_destr");
  klee_trace_param_fptr(dexk, "dexk");
  klee_trace_param_fptr(dpk, "dpk");
  klee_trace_param_i32(capacity, "capacity");
  klee_trace_param_i32(keys_capacity, "keys_capacity");
  klee_trace_param_ptr_directed(map_out, sizeof(struct DoubleMap*), "map_out", TD_OUT);

  // TODO no need for this if malloc can fail
  int allocation_succeeded = klee_int("dmap_allocation_succeeded");
  *map_out = malloc(sizeof(struct DoubleMap));
  if (allocation_succeeded && *map_out != NULL) {
    memset(*map_out, 0, sizeof(struct DoubleMap));
    klee_assert(value_size < prealloc_size);

    (*map_out)->eq_a_g = eq_a;
    (*map_out)->eq_b_g = eq_b;
    (*map_out)->dexk_g = dexk;
    (*map_out)->dpk_g = dpk;
    (*map_out)->value_size_g = value_size;
    (*map_out)->has_this_key = klee_int("dmap_has_this_key");
    (*map_out)->entry_claimed = 0;
    (*map_out)->allocated_index = klee_int("dmap_allocated_index");
    klee_assume(0 <= (*map_out)->allocated_index);
    klee_assume((*map_out)->allocated_index < capacity);
    uint8_t value_symbol[prealloc_size];
    klee_make_symbolic(value_symbol, prealloc_size, "dmap_value");
    memcpy((*map_out)->value, value_symbol, prealloc_size);

    // Do not assume the ent_cond here, because depending on what comes next,
    // we may change the key_a, key_b or value. we assume the condition after
    // that change.

    DENY(*map_out);
    return 1;
  }
  return 0;
}

int dmap_get_a(struct DoubleMap* map, void* key, int* index) {
  ALLOW(map);
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_ptr(key, map->key_a_size_g, "key");
  klee_trace_param_ptr(index, sizeof(int), "index");
  {
    for (int i = 0; i < map->key_a_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 map->key_a_fields[i].offset,
                                 map->key_a_fields[i].width,
                                 map->key_a_fields[i].name);
    }
  }

  if (map->has_this_key) {
    klee_assert(!map->entry_claimed);
    void* key_a = NULL;
    void* key_b = NULL;
    map->dexk_g(map->value, &key_a, &key_b);

    klee_assume(map->eq_a_g(key_a, key));
    if (map->ent_cond)
      klee_assume(map->ent_cond(key_a, key_b,
                           map->allocated_index, map->value));
    map->dpk_g(map->value, key_a, key_b);
    map->entry_claimed = 1;
    *index = map->allocated_index;
    DENY(map);
    return 1;
  }
  DENY(map);
  return 0;
}

int dmap_get_b(struct DoubleMap* map, void* key, int* index) {
  ALLOW(map);
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_ptr(key, map->key_b_size_g, "key");
  klee_trace_param_ptr(index, sizeof(int), "index");
  {
    for (int i = 0; i < map->key_b_field_count; ++i) {
      klee_trace_param_ptr_field(key,
                                 map->key_b_fields[i].offset,
                                 map->key_b_fields[i].width,
                                 map->key_b_fields[i].name);
    }
  }

  if (map->has_this_key) {
    klee_assert(!map->entry_claimed);
    void* key_a = NULL;
    void* key_b = NULL;
    map->dexk_g(map->value, &key_a, &key_b);
    klee_assume(map->eq_b_g(key_b, key));
    if (map->ent_cond) klee_assume(map->ent_cond(key_a, key_b,
                                       map->allocated_index, map->value));
    map->dpk_g(map->value, key_a, key_b);
    map->entry_claimed = 1;
    *index = map->allocated_index;
    DENY(map);
    return 1;
  }
  DENY(map);
  return 0;
}

int dmap_put(struct DoubleMap* map, void* value_, int index) {
  ALLOW(map);
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_ptr(value_, map->value_size_g, "value_");
  klee_trace_param_i32(index, "index");
  {
    for (int i = 0; i < map->value_field_count; ++i) {
      klee_trace_param_ptr_field(value_,
                                 map->value_fields[i].offset,
                                 map->value_fields[i].width,
                                 map->value_fields[i].name);
    }
  }
  {
    for (int i = 0; i < map->value_nests_count; ++i) {
      klee_trace_param_ptr_nested_field(value_,
                                        map->value_nests[i].base_offset,
                                        map->value_nests[i].offset,
                                        map->value_nests[i].width,
                                        map->value_nests[i].name);
    }
  }

  // Can not ever fail, because index is guaranteed to point to the available
  // slot, therefore the map can not be full at this point.
  // Always returns 1.
  if (map->entry_claimed) {
    klee_assert(map->allocated_index == index);
  }
  memcpy(map->value, value_, map->value_size_g);
  void* key_a = 0;
  void* key_b = 0;
  map->dexk_g(map->value, &key_a, &key_b);
  // This must be provided by the caller, since it his responsibility
  // to fulfill the value by the same index:
  klee_assert(map->ent_cond == NULL || map->ent_cond(key_a, key_b,
                                           index,
                                           map->value));
  map->dpk_g(map->value, key_a, key_b);
  map->entry_claimed = 1;
  map->allocated_index = index;
  DENY(map);
  return 1;
}

int dmap_erase(struct DoubleMap* map, int index) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_i32(index, "index");

  klee_assert(map != NULL);
  klee_assert(0); //This model does not support erasure.
  return 0;
}

void dmap_get_value(struct DoubleMap* map, int index, void* value_out) {
  ALLOW(map);
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_trace_param_i32(index, "index");
  klee_trace_param_ptr_directed(value_out, map->value_size_g, "value_out", TD_OUT);
  {
    for (int i = 0; i < map->value_field_count; ++i) {
      klee_trace_param_ptr_field_directed(value_out,
                                          map->value_fields[i].offset,
                                          map->value_fields[i].width,
                                          map->value_fields[i].name,
                                          TD_OUT);
    }
  }
  {
    for (int i = 0; i < map->value_nests_count; ++i) {
      klee_trace_param_ptr_nested_field_directed(value_out,
                                                 map->value_nests[i].base_offset,
                                                 map->value_nests[i].offset,
                                                 map->value_nests[i].width,
                                                 map->value_nests[i].name,
                                                 TD_OUT);
    }
  }

  if (map->entry_claimed) {
    klee_assert(index == map->allocated_index);
  } else {
    map->allocated_index = index;
    map->entry_claimed = 1;
  }
  memcpy(value_out, map->value, map->value_size_g);
  DENY(map);
}

int dmap_size(struct DoubleMap* map) {
  klee_trace_ret();
  //To avoid symbolic-pointer-dereference,
  // consciously trace "map" as a simple value.
  klee_trace_param_u64((uint64_t)map, "map");
  klee_assert(0); //This model does not support size requests.
  return -1;
}

void dmap_reset(struct DoubleMap* map, int capacity) {
  ALLOW(map);
  map->entry_claimed = 0;
  klee_assume(0 <= map->allocated_index);
  klee_assume(map->allocated_index < capacity);
  DENY(map);
}
