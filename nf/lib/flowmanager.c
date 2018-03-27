#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include "flowtable.h"
#include "lib/containers/double-chain.h"
#include "flowmanager.h"
#include "lib/expirator.h"

#ifdef KLEE_VERIFICATION
#  include <rte_ethdev.h>
#  include "lib/stubs/containers/double-map-stub-control.h" //<- for set entry cond
#endif //KLEE_VERIFICATION

struct FlowManager {
    uint16_t starting_port;
    uint32_t ext_src_ip;
    uint16_t ext_device_id;
    uint32_t expiration_time; /*seconds*/
    struct DoubleChain* chain;
    struct DoubleMap* flow_table;
};

#ifdef KLEE_VERIFICATION
struct DoubleChain** get_dchain_pp(struct FlowManager* manager) {
  return &(manager->chain);
}

struct DoubleMap** get_dmap_pp(struct FlowManager* manager) {
  return &(manager->flow_table);
}

void concretize_devices(struct flow* f) {
    int count = rte_eth_dev_count();

    klee_assume(f->int_device_id >= 0);
    klee_assume(f->ext_device_id >= 0);
    klee_assume(f->int_device_id < count);
    klee_assume(f->ext_device_id < count);

    for(unsigned d = 0; d < count; d++) if (f->int_device_id == d) { f->int_device_id = d; break; }
    for(unsigned d = 0; d < count; d++) if (f->ext_device_id == d) { f->ext_device_id = d; break; }
}
#endif//KLEE_VERIFICATION

struct FlowManager* allocate_flowmanager(uint16_t nb_ports,
                                         uint16_t starting_port,
                                         uint32_t ext_src_ip,
                                         uint16_t ext_device_id,
                                         uint32_t expiration_time,
                                         int max_flows) {
#ifdef KLEE_VERIFICATION
    // HACK HACK HACK HACK only works if the two starting ports are the same (see definition in flow.h)
    GLOBAL_starting_port = starting_port;
#endif//KLEE_VERIFICATION

    struct FlowManager* manager = (struct FlowManager*) malloc(sizeof(struct FlowManager));
    if (manager == NULL) {
        return NULL;
    }

    manager->starting_port = starting_port;
    manager->ext_src_ip = ext_src_ip;
    manager->ext_device_id = ext_device_id;
    manager->expiration_time = expiration_time; /*seconds*/

    if (0 == allocate_flowtables(nb_ports, max_flows, &(manager->flow_table))) {
        free(manager);
        return NULL;
    }

    if (0 == dchain_allocate(max_flows, &(manager->chain))) {
        free(manager->flow_table);
        free(manager);
        return NULL;
    }

#ifdef KLEE_VERIFICATION
    dmap_set_entry_condition(manager->flow_table, flow_consistency);
#endif

    return manager;
}

int allocate_flow(struct FlowManager* manager, struct int_key *k, time_t time, struct flow* out) {
    int index = -1;
    int alloc_rez = dchain_allocate_new_index(manager->chain, &index, time);
    if (0 == alloc_rez) return 0; //Out of resources.
    uint16_t port = manager->starting_port + index;
    //klee_assert(k->int_device_id != ext_device_id);
    struct flow new_flow = {
        .int_src_port = k->int_src_port,
        .ext_src_port = port,
        .dst_port = k->dst_port,
        .int_src_ip = k->int_src_ip,
        .ext_src_ip = manager->ext_src_ip,
        .dst_ip = k->dst_ip,
        .int_device_id = k->int_device_id,
        .ext_device_id = manager->ext_device_id,
        .protocol = k->protocol,
    };
    if (!add_flow(manager->flow_table, &new_flow, index)) return 0;
    get_flow(manager->flow_table, index, out);
    return 1;
}

static
void get_and_rejuvenate(struct FlowManager* manager, int index, time_t time, struct flow* flow_out) {
  get_flow(manager->flow_table, index, flow_out);
  dchain_rejuvenate_index(manager->chain, index, time);

#ifdef KLEE_VERIFICATION
  concretize_devices(flow_out);
#endif
}

int get_flow_by_int_key(struct FlowManager* manager, struct int_key* key, time_t time, struct flow* flow_out) {
  int index = -1;
  if (!get_flow_int(manager->flow_table, key, &index))
    return 0;
  get_and_rejuvenate(manager, index, time, flow_out);
  return 1;
}

int get_flow_by_ext_key(struct FlowManager* manager, struct ext_key* key, time_t time, struct flow* flow_out) {
  int index = -1;
  if (!get_flow_ext(manager->flow_table, key, &index))
    return 0;
  get_and_rejuvenate(manager, index, time, flow_out);
  return 1;
}

int expire_flows(struct FlowManager* manager, time_t time) {
  //VV too early, nothing can expire yet.
  if (time < manager->expiration_time) return 0;

  // This is convoluted - we want to make sure the sanitization doesn't
  // extend our time_t value in 128 bits, which would confuse the validator.
  // So we "prove" by hand that it's OK...
  if (time < 0) return 0; // we don't support the past
  assert(sizeof(time_t) <= sizeof(uint64_t));
  uint64_t time_u = (uint64_t) time; // OK since assert above passed and time > 0
  uint64_t last_time_u = time_u - manager->expiration_time; // OK because time >= expiration_time >= 0
  assert(sizeof(uint64_t) <= sizeof(time_t));
  time_t last_time = (time_t) last_time_u; // OK since the assert above passed
  return expire_items(manager->chain, manager->flow_table, last_time);
}
