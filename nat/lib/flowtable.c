#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <rte_log.h>

#include "containers/double-map.h"
#include "flowtable.h"

#ifdef KLEE_VERIFICATION
#  include "stubs/containers/double-map-stub-control.h"
#endif //KLEE_VERIFICATION

#if MAX_FLOWS > DMAP_CAPACITY
#  error "The map static capacity is insufficient for this number of flows"
#endif

#ifndef RTE_LOG_LEVEL
#  define RTE_LOG_LEVEL RTE_LOG_INFO
#endif //RTE_LOG_LEVEL
#define RTE_LOGTYPE_NAT RTE_LOGTYPE_USER1

#define LOG(...) RTE_LOG(INFO, NAT, __VA_ARGS__)
#define LOG_ADD(...) printf(__VA_ARGS__)

struct flow* get_flow(int index) {
  return (struct flow*)dmap_get_value(index);
}

int get_flow_int(struct int_key* key, int* index) {
    LOG("look up for internal key key = \n");
    log_int_key(key);
    return dmap_get_a(key, index);
}

int get_flow_ext(struct ext_key* key, int* index) {
    LOG("look up for external key key = \n");
    log_ext_key(key);
    return dmap_get_b(key, index);
}

static inline void fill_int_key(struct flow *f, struct int_key *k) {
    k->int_src_port = f->int_src_port;
    k->dst_port = f->dst_port;
    k->int_src_ip = f->int_src_ip;
    k->dst_ip = f->dst_ip;
    k->int_device_id = f->int_device_id;
    k->protocol = f->protocol;
}

static inline void fill_ext_key(struct flow *f, struct ext_key *k) {
    k->ext_src_port = f->ext_src_port;
    k->dst_port = f->dst_port;
    k->ext_src_ip = f->ext_src_ip;
    k->dst_ip = f->dst_ip;
    k->ext_device_id = f->ext_device_id;
    k->protocol = f->protocol;
}

//Warning: this is thread-unsafe, do not youse more than 1 lcore!
int add_flow(struct flow *f, int index) {
    assert(0 <= index && index < MAX_FLOWS);
    LOG("add_flow (f = \n");
    log_flow(f);
    struct flow *new_flow = get_flow(index);
    *new_flow = *f;
    struct int_key* new_int_key = &new_flow->ik;
    struct ext_key* new_ext_key = &new_flow->ek;
    fill_int_key(f, new_int_key);
    fill_ext_key(f, new_ext_key);

    //assert(get_flow_ext(new_ext_key) == NULL);
    //assert(get_flow_int(new_int_key) == NULL);

    return dmap_put(new_int_key, new_ext_key, index);
}

int remove_flow(int index) {
    assert(0 <= index && index < MAX_FLOWS);
    struct flow* f = get_flow(index);
    return dmap_erase(&f->ik, &f->ek);
}

#ifdef KLEE_VERIFICATION
int flow_consistency(void* key_a, void* key_b, void* value) {
  struct int_key* int_key = key_a;
  struct ext_key* ext_key = key_b;
  struct flow* flow = value;
  return
    int_key->int_src_port == flow->int_src_port &&
    int_key->dst_port == flow->dst_port &&
    int_key->int_src_ip == flow->int_src_ip &&
    int_key->dst_ip == flow->dst_ip &&
    int_key->int_device_id == flow->int_device_id &&
    int_key->protocol == flow->protocol &&
    (0 == memcmp(int_key, &flow->ik, sizeof(struct int_key))) &&
    ext_key->ext_src_port == flow->ext_src_port &&
    ext_key->dst_port == flow->dst_port &&
    ext_key->ext_src_ip == flow->ext_src_ip &&
    ext_key->dst_ip == flow->dst_ip &&
    ext_key->ext_device_id == flow->ext_device_id &&
    ext_key->protocol == flow->protocol &&
    (0 == memcmp(ext_key, &flow->ek, sizeof(struct ext_key)));
}
#endif //KLEE_VERIFICATION

int allocate_flowtables(uint8_t nb_ports) {
    (void)nb_ports;
#ifdef KLEE_VERIFICATION
    dmap_set_entry_condition(flow_consistency);
#endif //KLEE_VERIFICATION
    return dmap_allocate(sizeof(struct int_key), sizeof(struct ext_key),
                         sizeof(struct flow));
}

