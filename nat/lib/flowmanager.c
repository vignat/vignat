#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include "flowtable.h"
#include "containers/double-chain.h"
#include "flowmanager.h"
#include "expirator.h"

#ifdef KLEE_VERIFICATION
#  include "stubs/rte_stubs.h" //<- for RTE_MAX_ETHPORTS
#  include "stubs/containers/double-map-stub-control.h" //<- for set entry cond
#endif //KLEE_VERIFICATION


uint16_t starting_port = 0;
uint32_t ext_src_ip = 0;
uint8_t ext_device_id = 0;
uint32_t expiration_time = 0; /*seconds*/
struct DoubleChain* chain;

#ifdef KLEE_VERIFICATION
int flow_consistency(void* key_a, void* key_b, int index, void* value) {
  struct int_key* int_key = key_a;
  struct ext_key* ext_key = key_b;
  struct flow* flow = value;
  return
#if 0 //Semantic - inessential for the crash-freedom.
    ( int_key->int_src_port == flow->int_src_port ) &
    ( int_key->dst_port == flow->dst_port ) &
    ( int_key->int_src_ip == flow->int_src_ip ) &
    ( int_key->dst_ip == flow->dst_ip ) &
    ( int_key->int_device_id == flow->int_device_id ) &
    ( int_key->protocol == flow->protocol ) &

    ( int_key->int_src_port == flow->ik.int_src_port ) &
    ( int_key->dst_port == flow->ik.dst_port ) &
    ( int_key->int_src_ip == flow->ik.int_src_ip ) &
    ( int_key->dst_ip == flow->ik.dst_ip ) &
    ( int_key->int_device_id == flow->ik.int_device_id ) &
    ( int_key->protocol == flow->ik.protocol ) &

    //(0 == memcmp(int_key, &flow->ik, sizeof(struct int_key))) &
    ( ext_key->ext_src_port == flow->ext_src_port ) &
    ( ext_key->dst_port == flow->dst_port ) &
    ( ext_key->ext_src_ip == flow->ext_src_ip ) &
    ( ext_key->dst_ip == flow->dst_ip ) &
    ( ext_key->ext_device_id == flow->ext_device_id ) &
    ( ext_key->protocol == flow->protocol ) &

    ( ext_key->ext_src_port == flow->ek.ext_src_port ) &
    ( ext_key->dst_port == flow->ek.dst_port ) &
    ( ext_key->ext_src_ip == flow->ek.ext_src_ip ) &
    ( ext_key->dst_ip == flow->ek.dst_ip ) &
    ( ext_key->ext_device_id == flow->ek.ext_device_id ) &
    ( ext_key->protocol == flow->ek.protocol ) &
#endif//0 -- inessential for crash freedom part.
    ( 0 <= flow->int_device_id) &
          (flow->int_device_id < RTE_MAX_ETHPORTS) &
    ( 0 <= flow->ext_device_id) &
          (flow->ext_device_id < RTE_MAX_ETHPORTS) &
    ( ext_key->ext_src_port == starting_port + index) &
    ( flow->ext_src_port == starting_port + index ) &
    ( flow->ek.ext_src_port == starting_port + index );
    //(0 == memcmp(ext_key, &flow->ek, sizeof(struct ext_key)));
}

struct DoubleChain** get_dchain_pp(void) {
  return &chain;
}

#endif//KLEE_VERIFICATION

int allocate_flowmanager(uint8_t nb_ports,
                         uint16_t _starting_port, uint32_t _ext_src_ip,
                         uint8_t _ext_device_id,
                         uint32_t _expiration_time) {
#ifdef KLEE_VERIFICATION
    dmap_set_entry_condition(flow_consistency);
#endif//KLEE_VERIFICATION
    if (0 == allocate_flowtables(nb_ports))
        return 0;
    starting_port = _starting_port;
    ext_src_ip = _ext_src_ip;
    ext_device_id = _ext_device_id;
    expiration_time = _expiration_time;
    if (0 == dchain_allocate(MAX_FLOWS, &chain))
        return 0;
    return 1;
}

int allocate_flow(struct int_key *k, uint32_t time, struct flow* out) {
    int index = -1;
    int alloc_rez = dchain_allocate_new_index(chain, &index, time);
    if (0 == alloc_rez) return 0; //Out of resources.
    uint16_t port = starting_port + index;
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
