#include <stdlib.h>

#include "double-chain.h"
#include "double-chain-impl.h"

struct DoubleChain {
  struct dchain_cell* cells;
  uint32_t *timestamps;
};

int dchain_allocate(int index_range, struct DoubleChain** chain_out) {

  if (NULL == (*chain_out = malloc(sizeof(struct DoubleChain)))) return 0;
  if (NULL == ((**chain_out).cells = malloc(sizeof(struct dchain_cell)*
                                             (index_range + DCHAIN_RESERVED))))
    return 0;
  if (NULL == ((**chain_out).timestamps =
               malloc(sizeof(uint32_t)*index_range)))
    return 0;
  dchain_impl_init((**chain_out).cells, index_range);
  return 1;
}

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int *index_out, uint32_t time) {
  int ret = dchain_impl_allocate_new_index(chain->cells, index_out);
  if (ret) chain->timestamps[*index_out] = time;
  return ret;
}

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time) {
  int ret = dchain_impl_rejuvenate_index(chain->cells, index);
  if (ret) {
    if (chain->timestamps[index] > time) return 0;
    chain->timestamps[index] = time;
  }
  return ret;
}

int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time) {
  int has_ind = dchain_impl_get_oldest_index(chain->cells, index_out);
  if (has_ind) {
    if (chain->timestamps[*index_out] > time) {
      return dchain_impl_free_index(chain->cells, *index_out);
    }
  }
  return 0;
}
