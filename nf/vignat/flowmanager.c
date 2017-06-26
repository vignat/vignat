#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include "flowtable.h"
#include "lib/containers/double-chain.h"
#include "flowmanager.h"
#include "lib/expirator.h"

#ifdef KLEE_VERIFICATION
#  include "lib/stubs/rte_stubs.h" //<- for RTE_MAX_ETHPORTS
#  include "lib/stubs/containers/double-map-stub-control.h" //<- for set entry cond
#endif //KLEE_VERIFICATION


uint16_t starting_port = 0;
uint32_t ext_src_ip = 0;
uint8_t ext_device_id = 0;
uint32_t expiration_time = 0; /*seconds*/
struct DoubleChain* chain;

#ifdef KLEE_VERIFICATION
struct DoubleChain** get_dchain_pp(void) {
  return &chain;
}

#endif//KLEE_VERIFICATION

int allocate_flowmanager(uint8_t nb_ports,
                         uint16_t _starting_port, uint32_t _ext_src_ip,
                         uint8_t _ext_device_id,
                         uint32_t _expiration_time,
                         int max_flows) {
#ifdef KLEE_VERIFICATION
    dmap_set_entry_condition(flow_consistency);
#endif//KLEE_VERIFICATION
    if (0 == allocate_flowtables(nb_ports, max_flows))
        return 0;
    starting_port = _starting_port;
    ext_src_ip = _ext_src_ip;
    ext_device_id = _ext_device_id;
    expiration_time = _expiration_time;
    if (0 == dchain_allocate(max_flows, &chain))
        return 0;
    return 1;
}

int allocate_flow(struct int_key *k, uint32_t time, struct flow* out) {
    int index = -1;
    int alloc_rez = dchain_allocate_new_index(chain, &index, time);
    if (0 == alloc_rez) return 0; //Out of resources.
    uint16_t port = starting_port + index;
    //klee_assert(k->int_device_id != ext_device_id);
    struct flow new_flow = {
        .int_src_port = k->int_src_port,
        .ext_src_port = port,
        .dst_port = k->dst_port,
        .int_src_ip = k->int_src_ip,
        .ext_src_ip = ext_src_ip,
        .dst_ip = k->dst_ip,
        .int_device_id = k->int_device_id,
        .ext_device_id = ext_device_id,
        .protocol = k->protocol,
    };
    if (!add_flow(&new_flow, index)) return 0;
    get_flow(index, out);
    return 1;
}

static
void get_and_rejuvenate(int index, uint32_t time, struct flow* flow_out) {
  get_flow(index, flow_out);
  dchain_rejuvenate_index(chain, index, time);
}

int get_flow_by_int_key(struct int_key* key, uint32_t time, struct flow* flow_out) {
  int index = -1;
  if (!get_flow_int(key, &index))
    return 0;
  get_and_rejuvenate(index, time, flow_out);
  return 1;
}

int get_flow_by_ext_key(struct ext_key* key, uint32_t time, struct flow* flow_out) {
  int index = -1;
  if (!get_flow_ext(key, &index))
    return 0;
  get_and_rejuvenate(index, time, flow_out);
  return 1;
}

int expire_flows(uint32_t time) {
  //VV too early, nothing can expire yet.
  if (time < expiration_time) return 0;
  uint32_t last_time = time - expiration_time;
  return expire_items(chain, get_flow_table(), last_time);
}
