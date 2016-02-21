#include <assert.h>
#include "containers/double-chain.h"
#include "flowtable.h"
#include "expirator.h"

int expire_items(struct DoubleChain* chain, struct DoubleMap* map, uint32_t time) {
  int count = 0;
  int index = -1;
  while (dchain_expire_one_index(chain, &index, time)) {
    dmap_erase(map, index);
    ++count;
  }
  return count;
}

