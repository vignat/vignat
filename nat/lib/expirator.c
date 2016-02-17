#include <assert.h>
#include "containers/double-chain.h"
#include "flowtable.h"
#include "expirator.h"

uint32_t expiration_time = 0; /*seconds*/

void init_expirator(uint32_t exp_time) {
    expiration_time = exp_time;
}

int expire_flows(uint32_t time) {
    /* too early to bother about expiration */
    if (time < expiration_time) return 0;
    uint32_t expired = time - expiration_time;
    int count = 0;
    int index = -1;
    while (dchain_get_oldest_index(&index)) {
      struct flow f;
      get_flow(index, &f);
      uint32_t t = f.timestamp;
      if (t > expired) break;
      remove_flow(index);
      int rez = dchain_free_index(index);
      assert(1 == rez);
      ++count;
    }
    return count;
}

