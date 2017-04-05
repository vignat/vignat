#include <inttypes.h>
#include <assert.h>

// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <rte_ethdev.h>
#include <rte_mbuf.h>

#include "lib/nat_config.h"
#include "lib/nf_forward.h"
#include "lib/nf_util.h"
#include "lib/nf_log.h"

struct nat_config config;

//const int CAPACITY = 1e3;
#define CAPACITY 1000
const uint32_t EXP_TIME = 3;//seconds TODO: should be 300s, but that's tough to test

struct mac_map {
  int busybits[CAPACITY];
  void* keyps[CAPACITY];
  int khs[CAPACITY];
  int chns[CAPACITY];
  int vals[CAPACITY];
  int devices[CAPACITY];
  struct ether_addr keys[CAPACITY];
  int size;
} map;

struct DoubleChain* heap;

int ether_addr_eq(struct ether_addr* a,
                  struct ether_addr* b) {
  return 0 == memcmp(a->addr_bytes,
                     b->addr_bytes,
                     6);
}

int ether_addr_hash(struct ether_addr* addr) {
  return (int)((*(uint32_t*)addr->addr_bytes) ^
               (*(uint32_t*)(addr->addr_bytes + 2)));
}

int mac_map_get_device(struct ether_addr* dst) {
  int index = -1;
  int hash = ether_addr_hash(dst);
  int present = map_get(map.busybits, map.keyps, map.khs,
                        map.chns, map.vals,
                        dst, ether_addr_eq, hash, &index,
                        CAPACITY);
  if (present) {
    return map.devices[index];
  }
  return -1;
}

void mac_map_remember_device(struct ether_addr* src,
                             int device, uint32_t time) {
  assert(mac_map_get_device(src) == -1);
  int hash = ether_addr_hash(src);
  int index = 0;
  int allocated = dchain_allocate_new_index(heap, &index, time);
  assert(allocated);
  memcpy(&map.keys[index], src, sizeof(struct ether_addr));
  map_put(map.busybits, map.keyps, map.khs, map.chns,
          map.vals, &map.keys[index], hash, index, CAPACITY);
  map.devices[index] = device;
}

void mac_map_add_update_entry(struct ether_addr* src,
                              int device, uint32_t time) {
  int index = -1;
  int hash = ether_addr_hash(src);
  int present = map_get(map.busybits, map.keyps, map.khs,
                        map.chns, map.vals,
                        src, ether_addr_eq, hash, &index,
                        CAPACITY);
  if (present) {
    dchain_rejuvenate_index(heap, index, time);
  } else {
    mac_map_remember_device(src, device, time);
  }
}

int mac_map_expire_entries(uint32_t time) {
  int count = 0;
  int index = -1;
  void *trash;
  if (time < EXP_TIME) return 0;
  uint32_t oldest_time = time - EXP_TIME;
  while (dchain_expire_one_index(heap, &index, oldest_time)) {
    int hash = ether_addr_hash(&map.keys[index]);
    map_erase(map.busybits, map.keyps, map.khs,
              map.chns, &map.keys[index],
              ether_addr_eq, hash,
              CAPACITY, &trash);
    ++count;
  }
  return count;
}

void nf_core_init(void)
{
  memset(map.keys, 0, CAPACITY);
  map_initialize(map.busybits, ether_addr_eq,
                 map.keyps, map.khs, map.chns,
                 map.vals, CAPACITY);
  map.size = 0;
  dchain_allocate(CAPACITY, &heap);
}

int nf_core_process(uint8_t device,
                    struct rte_mbuf* mbuf,
                    uint32_t now)
{
  struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

  mac_map_expire_entries(now);
  mac_map_add_update_entry(&ether_header->s_addr, device, now);

  int dst_device = mac_map_get_device(&ether_header->d_addr);

  if (dst_device == -1) {
    return FLOOD_FRAME;
  }

  if (dst_device == -2) {
    NF_DEBUG("filtered frame");
    return device;
  }

  return dst_device;
}

void nf_config_init(int argc, char** argv) {
  nat_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  nat_config_cmdline_print_usage();
}

void nf_print_config() {
  nat_print_config(&config);
}
