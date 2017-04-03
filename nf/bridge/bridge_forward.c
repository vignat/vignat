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

struct mac_map {
  int busybits[CAPACITY];
  void* keyps[CAPACITY];
  int khs[CAPACITY];
  int chns[CAPACITY];
  int vals[CAPACITY];
  struct ether_addr keys[CAPACITY];
  int size;
} map;

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
  int port = -1;
  int hash = ether_addr_hash(dst);
  int present = map_get(map.busybits, map.keyps, map.khs,
                        map.chns, map.vals,
                        dst, ether_addr_eq, hash, &port,
                        CAPACITY);
  if (present) {
    return port;
  }
  return -1;
}

void mac_map_remember_device(struct ether_addr* src,
                             int port) {
  assert(mac_map_get_device(src) == -1);
  int hash = ether_addr_hash(src);
  map_put(map.busybits, map.keyps, map.khs, map.chns,
          map.vals, src, hash, port, CAPACITY);
}

void nf_core_init(void)
{
  memset(map.keys, 0, CAPACITY);
  map_initialize(map.busybits, ether_addr_eq,
                 map.keyps, map.khs, map.chns,
                 map.vals, CAPACITY);
  map.size = 0;
}

int nf_core_process(uint8_t device,
                    struct rte_mbuf* mbuf,
                    uint32_t now)
{
	(void) now;

  struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

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
