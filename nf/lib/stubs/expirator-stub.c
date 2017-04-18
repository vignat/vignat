#include <klee/klee.h>
#include "lib/expirator.h"
#include "containers/double-chain-stub-control.h"

int expire_items(struct DoubleChain* chain, struct DoubleMap* map,
                 uint32_t time) {
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)chain, "chain");
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_i32(time, "exp_time");
  int nfreed = klee_int("number_of_freed_flows");
  klee_assume(0 <= nfreed);
  if (nfreed > 0) {
    dchain_make_space(chain);
  }
  //Tell dchain model that we freed some indexes here
  return nfreed;
}

int expire_items_single_map(struct DoubleChain* chain,
                            struct Vector* vector,
                            struct Map* map,
                            entry_extract_key* eek,
                            entry_pack_key* epk,
                            uint32_t time) {
  klee_trace_ret();
  klee_trace_param_i32((uint32_t)chain, "chain");
  klee_trace_param_i32((uint32_t)vector, "vector");
  klee_trace_param_i32((uint32_t)map, "map");
  klee_trace_param_fptr(eek, "eek");
  klee_trace_param_fptr(epk, "epk");
  klee_trace_param_i32(time, "time");
  int nfreed = klee_int("unmber_of_freed_flows");
  klee_assume(0 <= nfreed);
  if (0 < nfreed) {
    dchain_make_space(chain);
  }
  return nfreed;
}
