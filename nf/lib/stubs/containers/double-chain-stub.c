#include <assert.h>
#include <klee/klee.h>
#include "lib/containers/double-chain.h"

// TODO: double check that this model is enough for the NAT scenario

int is_dchain_allocated;
int out_of_space;
int new_index;
int is_index_allocated;

struct DoubleChain* allocated_chain;

int dchain_allocate(int index_range, struct DoubleChain** chain_out) {
    klee_trace_ret();
    klee_trace_param_i32(index_range, "index_range");
    klee_trace_param_ptr(chain_out, sizeof(struct DoubleChain*), "chain_out");

    is_dchain_allocated = klee_int("is_dchain_allocated");

    if (is_dchain_allocated) {
      klee_make_symbolic(&allocated_chain, sizeof(struct DoubleChain*),
                         "allocated_chain_do_not_dereference");
      *chain_out = allocated_chain;
      new_index = klee_int("new_index");
      klee_assume(0 <= new_index);
      klee_assume(new_index < index_range);
      is_index_allocated = 0;
      out_of_space = klee_int("out_of_space");
      return 1;
    } else {
      return 0;
    }
}

int dchain_allocate_new_index(struct DoubleChain* chain, int *index_out,
                              uint32_t time) {
    klee_trace_ret();
    //Deliberately trace this pointer as an integer to avoid
    // dereference.
    klee_trace_param_i32((uint32_t)chain, "chain");
    klee_trace_param_ptr(index_out, sizeof(int), "index_out");
    klee_trace_param_i32(time, "time");

    klee_assert(is_dchain_allocated);
    klee_assert(chain == allocated_chain);
    if (out_of_space) return 0;
    klee_assert(!is_index_allocated);
    *index_out = new_index;
    is_index_allocated = 1;
    return 1;
}

int dchain_rejuvenate_index(struct DoubleChain* chain, int index,
                            uint32_t time) {
    klee_trace_ret();
    //Deliberately trace this pointer as an integer to avoid
    // dereference.
    klee_trace_param_i32((uint32_t)chain, "chain");
    klee_trace_param_i32(index, "index");
    klee_trace_param_i32(time, "time");

    klee_assert(is_dchain_allocated);
    klee_assert(chain == allocated_chain);
    // TODO: Check if it is legible for rejuivenation?
    return 1;
}

int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time) {
  klee_trace_ret();
  //Deliberately trace this pointer as an integer to avoid
  // dereference.
  klee_trace_param_i32((uint32_t)chain, "chain");
  klee_trace_param_ptr(index_out, sizeof(int), "index_out");
  klee_trace_param_i32(time, "time");

  klee_assert(is_dchain_allocated);
  klee_assert(chain == allocated_chain);
  klee_assert(0 && "not supported in this model");
  return 0;
}

void dchain_make_space(struct DoubleChain* chain) {
  //Do not trace. this function is internal for the Expirator model.
  klee_assert(is_dchain_allocated);
  klee_assert(chain == allocated_chain);
  klee_assert(is_index_allocated == 0);
  //Do not trace internal stub control functions.
  out_of_space = 0;
}

void dchain_reset(struct DoubleChain* chain, int index_range) {
  //Do not trace. This function is an internal knob of the model.
  klee_assert(is_dchain_allocated);
  klee_assert(chain == allocated_chain);

  new_index = klee_int("new_index");
  klee_assume(0 <= new_index);
  klee_assume(new_index < index_range);
  is_index_allocated = 0;
  out_of_space = klee_int("out_of_space");
}
