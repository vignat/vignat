#include <string.h>
#include <assert.h>
#include "klee/klee.h"
#include "lib/containers/double-map.h"
#include "double-map-stub-control.h"

#define prealloc_size (256)

int key_a_size_g = 0;
int key_b_size_g = 0;
int value_size_g = 0;

uint8_t key_a[prealloc_size];
uint8_t key_b[prealloc_size];
uint8_t value[prealloc_size];
int allocation_succeeded;
int has_this_key;
int entry_claimed = 0;
int allocated_index;
entry_condition ent_cond = NULL;

void dmap_set_entry_condition(entry_condition c) {
  ent_cond = c;
}

int dmap_allocate(int key_a_size, int key_b_size, int value_size) {
  allocation_succeeded = klee_int("dmap_allocation_succeeded");
  if (allocation_succeeded) {
    klee_assert(key_a_size < prealloc_size);
    klee_assert(key_b_size < prealloc_size);
    klee_assert(value_size < prealloc_size);

    klee_make_symbolic(key_a, key_a_size, "dmap_key_a");
    klee_make_symbolic(key_b, key_b_size, "dmap_key_b");
    klee_make_symbolic(value, value_size, "dmap_value");

    has_this_key = klee_int("dmap_has_this_key");
    entry_claimed = 0;
    allocated_index = klee_int("dmap_claimed_index");

    key_a_size_g = key_a_size;
    key_b_size_g = key_b_size;
    value_size_g = value_size;
    // Do not assume the ent_cond here, because depending on what comes next,
    // we may change the key_a, key_b or value. we assume the condition after
    // that change.
    return 1;
  }
  return 0;
}

int dmap_get_a(void* key, int* index) {
  klee_assert(allocation_succeeded);
  if (has_this_key) {
    klee_assert(!entry_claimed);
    memcpy(key_a, key, key_a_size_g);
    klee_assume(ent_cond == NULL || ent_cond(key_a, key_b, value));
    entry_claimed = 1;
    *index = allocated_index;
    return 1;
  }
  return 0;
}

int dmap_get_b(void* key, int* index) {
  klee_assert(allocation_succeeded);
  if (has_this_key) {
    klee_assert(!entry_claimed);
    memcpy(key_b, key, key_b_size_g);
    klee_assume(ent_cond == NULL || ent_cond(key_a, key_b, value));
    entry_claimed = 1;
    *index = allocated_index;
    return 1;
  }
  return 0;
}

int dmap_put(void* key_a_, void* key_b_, int index) {
  // Can not ever fail, because index is guaranteed to point to the available
  // slot, therefore the map can not be full at this point.
  // Always returns 1.
  klee_assert(allocation_succeeded);
  klee_assert(!entry_claimed);
  memcpy(key_a, key_a_, key_a_size_g);
  memcpy(key_b, key_b_, key_b_size_g);
  // This must be handled bo the caller, since it his responsibility
  // to fulfill the value by the same index:
  //   klee_assume(ent_cond == NULL || ent_cond(key_a, key_b, value));
  entry_claimed = 1;
  allocated_index = index;
  return 1;
}

int dmap_erase(void* key_a, void* key_b) {
  klee_assert(allocation_succeeded);
  klee_assert(0); //This model does not support erasure.
  return 0;
}

void* dmap_get_value(int index) {
  klee_assert(allocation_succeeded);
  klee_assert(index == allocated_index);
  klee_assert(entry_claimed);
  return value;
}

int dmap_size() {
  klee_assert(0); //This model does not support size requests.
  return -1;
}
