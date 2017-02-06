#include "lib/containers/batcher.h"
#include <klee/klee.h>

int alloc_len;
int was_read;
BATCHER_EL_TYPE alloc_value[BATCHER_CAPACITY];
struct Batcher* batcher_initialized;

void batcher_init(struct Batcher* bat_out)
{
  // No need to trace this one, as it will be called from the inside of
  // another traced function, specifically:
  // array1_init -> array2_init -> batcher_init

  alloc_len = klee_range(0, BATCHER_CAPACITY, "batcher_alloc_len");
  klee_make_symbolic(alloc_value, BATCHER_CAPACITY*sizeof(BATCHER_EL_TYPE),
                     "batcher_alloc_value");
  was_read = 0;
  batcher_initialized = bat_out;
}

void batcher_push(struct Batcher *bat, BATCHER_EL_TYPE val)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(bat, sizeof(struct Batcher), "bat");
  klee_trace_param_just_ptr(val, sizeof(struct rte_mbuf), "val");

  klee_assert(bat == batcher_initialized);
  klee_assert(alloc_len < BATCHER_CAPACITY);
  alloc_len += 1;
  // Forget the value itself.
}

void batcher_take_all(struct Batcher *bat,
                      BATCHER_EL_TYPE **vals_out,
                      int *count_out)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(bat, sizeof(struct Batcher), "bat");
  //TODO: A proper tracing here.
  klee_trace_param_just_ptr(vals_out, sizeof(BATCHER_EL_TYPE*), "vals_out");
  klee_trace_param_ptr(count_out, sizeof(int), "count_out");

  klee_assert(bat == batcher_initialized);
  klee_assert(was_read == 0);
  was_read = 1;
  *vals_out = alloc_value;
  *count_out = alloc_len;
  alloc_len = 0;
}

void batcher_empty(struct Batcher *bat)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(bat, sizeof(struct Batcher), "bat");
  alloc_len = 0;
}

int batcher_full(struct Batcher *bat)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(bat, sizeof(struct Batcher), "bat");
  klee_assert(bat == batcher_initialized);
  // Explicit decision here, for validator to recognize 2 possibilities.
  if (BATCHER_CAPACITY <= alloc_len)
    return 1;
  return 0;
  //return BATCHER_CAPACITY <= alloc_len;
}

int batcher_is_empty(struct Batcher *bat)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(bat, sizeof(struct Batcher), "bat");
  klee_assert(bat == batcher_initialized);
  return alloc_len <= 0;
}
