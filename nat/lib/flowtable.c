#include <stddef.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <rte_log.h>

#include "containers/double-map.h"
#include "flowtable.h"

#ifdef KLEE_VERIFICATION
#  include "stubs/containers/double-map-stub-control.h"
#  include "stubs/my-time-stub-control.h"
#endif //KLEE_VERIFICATION

#ifdef KLEE_VERIFICATION
#  define LOG(...)
#  define LOG_ADD(...)
#else //KLEE_VERIFICATION
#  define RTE_LOGTYPE_NAT RTE_LOGTYPE_USER1
#  define LOG(...) RTE_LOG(INFO, NAT, __VA_ARGS__)
#  define LOG_ADD(...) printf(__VA_ARGS__)
#endif //KLEE_VERIFICATION

struct DoubleMap *flow_map;

void get_flow(int index, struct flow* flow_out) {
  dmap_get_value(flow_map, index, (char*)flow_out);
}

struct DoubleMap *get_flow_table(void) {
  return flow_map;
}

int get_flow_int(struct int_key* key, int* index) {
    LOG("look up for internal key key = \n");
    log_int_key(key);
    return dmap_get_a(flow_map, key, index);
}

int get_flow_ext(struct ext_key* key, int* index) {
    LOG("look up for external key key = \n");
    log_ext_key(key);
    return dmap_get_b(flow_map, key, index);
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
    LOG("add_flow (f = \n");
    log_flow(f);
    struct int_key* new_int_key = &f->ik;
    struct ext_key* new_ext_key = &f->ek;
    fill_int_key(f, new_int_key);
    fill_ext_key(f, new_ext_key);

    return dmap_put(flow_map, f, index);
}

#ifdef KLEE_VERIFICATION
struct str_field_descr int_key_descrs[] = {
  {offsetof(struct int_key, int_src_port), sizeof(uint16_t), "int_src_port"},
  {offsetof(struct int_key, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct int_key, int_src_ip), sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct int_key, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct int_key, int_device_id), sizeof(uint8_t), "int_device_id"},
  {offsetof(struct int_key, protocol), sizeof(uint8_t), "protocol"},
};
struct str_field_descr ext_key_descrs[] = {
  {offsetof(struct ext_key, ext_src_port), sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct ext_key, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct ext_key, ext_src_ip), sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct ext_key, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct ext_key, ext_device_id), sizeof(uint8_t), "ext_device_id"},
  {offsetof(struct ext_key, protocol), sizeof(uint8_t), "protocol"},
};
struct nested_field_descr flow_nests[] = {
  {offsetof(struct flow, ik), offsetof(struct int_key, int_src_port),
   sizeof(uint16_t), "int_src_port"},
  {offsetof(struct flow, ik), offsetof(struct int_key, dst_port),
   sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, ik), offsetof(struct int_key, int_src_ip),
   sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct flow, ik), offsetof(struct int_key, dst_ip),
   sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, ik), offsetof(struct int_key, int_device_id),
   sizeof(uint8_t), "int_device_id"},
  {offsetof(struct flow, ik), offsetof(struct int_key, protocol),
   sizeof(uint8_t), "protocol"},

  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_src_port),
   sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, dst_port),
   sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_src_ip),
   sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, dst_ip),
   sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_device_id),
   sizeof(uint8_t), "ext_device_id"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, protocol),
   sizeof(uint8_t), "protocol"},
};
struct str_field_descr flow_descrs[] = {
  {offsetof(struct flow, ik), sizeof(struct int_key), "ik"},
  {offsetof(struct flow, ek), sizeof(struct ext_key), "ek"},
  {offsetof(struct flow, int_src_port), sizeof(uint16_t), "int_src_port"},
  {offsetof(struct flow, ext_src_port), sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct flow, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, int_src_ip), sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct flow, ext_src_ip), sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct flow, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, int_device_id), sizeof(uint8_t), "int_device_id"},
  {offsetof(struct flow, ext_device_id), sizeof(uint8_t), "ext_device_id"},
  {offsetof(struct flow, protocol), sizeof(uint8_t), "protocol"},
};

struct DoubleMap **get_dmap_pp(void) {
  return &flow_map;
}

#endif //KLEE_VERIFICATION

int allocate_flowtables(uint8_t nb_ports, int max_flows) {
    (void)nb_ports;
#ifdef KLEE_VERIFICATION
    dmap_set_layout(int_key_descrs, sizeof(int_key_descrs)/sizeof(struct str_field_descr),
                    ext_key_descrs, sizeof(ext_key_descrs)/sizeof(struct str_field_descr),
                    flow_descrs, sizeof(flow_descrs)/sizeof(struct str_field_descr),
                    flow_nests, sizeof(flow_nests)/sizeof(struct nested_field_descr));
#endif //KLEE_VERIFICATION
    return dmap_allocate(int_key_eq, int_key_hash,
                         ext_key_eq, ext_key_hash,
                         sizeof(struct flow), flow_cpy,
                         flow_destroy,
                         flow_extract_keys,
                         flow_pack_keys,
                         max_flows,
                         &flow_map);
}

