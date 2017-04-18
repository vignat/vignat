#include <inttypes.h>
#include <string.h>

#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "lib/stubs/rte_stubs.h"
#  include <cmdline_parse_etheraddr.h>

#  include "lib/stubs/containers/map-stub-control.h"
#  include "lib/stubs/containers/double-chain-stub-control.h"
#  include "lib/stubs/containers/vector-stub-control.h"
#  include "lib/stubs/rte-stubs-control.h"
#else//KLEE_VERIFICATION
#  include <assert.h>
#  include <errno.h>
#  include <stdio.h>
// DPDK uses these but doesn't include them. :|
#  include <linux/limits.h>
#  include <sys/types.h>
#  include <unistd.h>
#  include <rte_ethdev.h>
#  include <rte_mbuf.h>
#endif//KLEE_VERIFICATION

#include "lib/nf_forward.h"
#include "lib/nf_util.h"
#include "lib/nf_log.h"
#include "bridge_config.h"

#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "lib/expirator.h"

struct bridge_config config;

struct StaticKey {
  struct ether_addr addr;
  uint8_t device;
};

struct DynamicEntry {
  struct ether_addr addr;
  uint8_t device;
};

struct DynamicFilterTable {
  struct Map* map;
  struct DoubleChain* heap;
  struct Vector* entries;
};

struct StaticFilterTable {
  struct Map* map;
  struct Vector* keys;
};

struct StaticFilterTable static_ft;
struct DynamicFilterTable dynamic_ft;

int ether_addr_eq(void* k1, void* k2) {
  struct ether_addr* a = (struct ether_addr*)k1;
  struct ether_addr* b = (struct ether_addr*)k2;
  return 0 == memcmp(a->addr_bytes,
                     b->addr_bytes,
                     6);
}

int static_key_eq(void* k1, void* k2) {
  struct StaticKey* a = (struct StaticKey*) k1;
  struct StaticKey* b = (struct StaticKey*) k2;
  return a->device == b->device && ether_addr_eq(&a->addr, &b->addr);

}

int ether_addr_hash(void* k) {
  struct ether_addr* addr = (struct ether_addr*)k;
  return (int)((*(uint32_t*)addr->addr_bytes) ^
               (*(uint32_t*)(addr->addr_bytes + 2)));
}

int static_key_hash(void* key) {
  struct StaticKey *k = (struct StaticKey*)key;
  return (ether_addr_hash(&k->addr) << 2) ^ k->device;
}

void dyn_entry_get_addr(void* entry,
                        void** addr_out) {
  *((struct ether_addr**)addr_out) = &((struct DynamicEntry*)entry)->addr;
}

int bridge_expire_entries(uint32_t time) {
  if (time < config.expiration_time) return 0;
  uint32_t min_time = time - config.expiration_time;
  return expire_items_single_map(dynamic_ft.heap, dynamic_ft.entries,
                                 dynamic_ft.map,
                                 dyn_entry_get_addr,
                                 min_time);
}

int bridge_get_device(struct ether_addr* dst,
                      uint8_t src_device) {
  int device = -1;
  struct StaticKey k;
  memcpy(&k.addr, dst, sizeof(struct ether_addr));
  k.device = src_device;
  int hash = static_key_hash(&k);
  int present = map_get(static_ft.map,
                        &k, &device);
  if (present) {
    return device;
  }
#ifdef KLEE_VERIFICATION
  map_reset(dynamic_ft.map);
  vector_reset(dynamic_ft.entries);
#endif//KLEE_VERIFICATION

  int index = -1;
  hash = ether_addr_hash(dst);
  present = map_get(dynamic_ft.map, dst, &index);
  if (present) {
    struct DynamicEntry* entry = vector_borrow(dynamic_ft.entries, index);
    device = entry->device;
    vector_return(dynamic_ft.entries, index, entry);
    return device;
  }
  return -1;
}

void bridge_put_update_entry(struct ether_addr* src,
                             uint8_t src_device,
                             uint32_t time) {
  int index = -1;
  int hash = ether_addr_hash(src);
  int present = map_get(dynamic_ft.map, src, &index);
  if (present) {
    dchain_rejuvenate_index(dynamic_ft.heap, index, time);
  } else {
    int allocated = dchain_allocate_new_index(dynamic_ft.heap,
                                              &index,
                                              time);
    if (!allocated) {
      NF_INFO("No more space in the dynamic table");
      return;
    }
    struct DynamicEntry* entry = vector_borrow(dynamic_ft.entries, index);
    memcpy(&entry->addr, src, sizeof(struct ether_addr));
    entry->device = src_device;
    map_put(dynamic_ft.map, &entry->addr, index);
    vector_return(dynamic_ft.entries, index, entry);
  }
}

void init_nothing(void* entry) {
  /* do nothing */
}

void allocate_static_ft(int capacity) {
  int happy = map_allocate(static_key_eq, static_key_hash,
                           capacity, &static_ft.map);

  if (!happy) rte_exit(EXIT_FAILURE, "error allocating static map");
  happy = vector_allocate(sizeof(struct StaticKey), capacity,
                          init_nothing,
                          &static_ft.keys);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating static array");
}
#ifdef KLEE_VERIFICATION

struct str_field_descr static_map_key_fields[] = {
  {offsetof(struct StaticKey, addr), sizeof(struct ether_addr), "addr"},
  {offsetof(struct StaticKey, device), sizeof(uint8_t), "device"},
};

struct str_field_descr dynamic_map_key_fields[] = {
  {0, sizeof(struct ether_addr), "value"}
};

struct str_field_descr static_vector_entry_fields[] = {
  {offsetof(struct StaticKey, addr), sizeof(struct ether_addr), "addr"},
  {offsetof(struct StaticKey, device), sizeof(uint8_t), "device"},
};

struct str_field_descr dynamic_vector_entry_fields[] = {
  {offsetof(struct StaticKey, addr), sizeof(struct ether_addr), "addr"},
  {offsetof(struct StaticKey, device), sizeof(uint8_t), "device"},
};

#endif//KLEE_VERIFICATION

#ifdef KLEE_VERIFICATION

void read_static_ft_from_file() {
  allocate_static_ft(klee_int("static_capacity"));
  map_set_layout(static_ft.map, static_map_key_fields,
                 sizeof(static_map_key_fields)/sizeof(static_map_key_fields[0]));
  vector_set_layout(static_ft.keys, static_vector_entry_fields,
                    sizeof(static_vector_entry_fields)/
                    sizeof(static_vector_entry_fields[0]));
}

#else//KLEE_VERIFICATION

void read_static_ft_from_file() {
  if (config.static_config_fname[0] == '\0') {
    // No static config
    allocate_static_ft(1);
    return;
  }

  FILE* cfg_file = fopen(config.static_config_fname, "r");
  if (cfg_file == NULL) {
    rte_exit(EXIT_FAILURE, "Error opening the static config file: %s",
             config.static_config_fname);
  }

  int number_of_lines = 0;
  char ch;
  do {
    ch = fgetc(cfg_file);
    if(ch == '\n')
      number_of_lines++;
  } while (ch != EOF);

  // Make sure the hash table is occupied only by 50%
  int capacity = number_of_lines * 2;
  rewind(cfg_file);
  allocate_static_ft(capacity);
  int count = 0;

  while (1) {
    char mac_addr_str[20];
    char source_str[10];
    char target_str[10];
    int result = fscanf(cfg_file, "%18s", mac_addr_str);
    if (result != 1) {
      if (result == EOF) break;
      else {
        NF_INFO("Cannot read MAC address from file: %s",
                strerror(errno));
        goto finally;
      }
    }

    result = fscanf(cfg_file, "%9s", source_str);
    if (result != 1) {
      if (result == EOF) {
        NF_INFO("Incomplete config string: %s, skip", mac_addr_str);
        break;
      } else {
        NF_INFO("Cannot read the filtering target for MAC %s: %s",
                mac_addr_str, strerror(errno));
        goto finally;
      }
    }

    result = fscanf(cfg_file, "%9s", target_str);
    if (result != 1) {
      if (result == EOF) {
        NF_INFO("Incomplete config string: %s, skip", mac_addr_str);
        break;
      } else {
        NF_INFO("Cannot read the filtering target for MAC %s: %s",
                mac_addr_str, strerror(errno));
        goto finally;
      }
    }

    int device_from;
    int device_to;
    char* temp;
    struct StaticKey* key = vector_borrow(static_ft.keys, count);

    // Ouff... the strings are extracted, now let's parse them.
    result = cmdline_parse_etheraddr(NULL, mac_addr_str,
                                     &key->addr,
                                     sizeof(struct ether_addr));
    if (result < 0) {
      NF_INFO("Invalid MAC address: %s, skip",
              mac_addr_str);
      continue;
    }

    device_from = strtol(source_str, &temp, 10);
    if (temp == source_str || *temp != '\0') {
      NF_INFO("Non-integer value for the forwarding rule: %s (%s), skip",
              mac_addr_str, target_str);
      continue;
    }

    device_to = strtol(target_str, &temp, 10);
    if (temp == target_str || *temp != '\0') {
      NF_INFO("Non-integer value for the forwarding rule: %s (%s), skip",
              mac_addr_str, target_str);
      continue;
    }

    // Now everything is alright, we can add the entry
    key->device = device_from;
    map_put(static_ft.map, &key->addr, device_to);
    vector_return(static_ft.keys, count, key);
    ++count;
    assert(count < capacity);
  }
 finally:
  fclose(cfg_file);
}

#endif//KLEE_VERIFICATION

void nf_core_init(void) {
  read_static_ft_from_file();

  int capacity = config.dyn_capacity;
  int happy = map_allocate(ether_addr_eq, ether_addr_hash,
                           capacity, &dynamic_ft.map);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic map");
  happy = dchain_allocate(capacity, &dynamic_ft.heap);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating heap");
  happy = vector_allocate(sizeof(struct DynamicEntry), capacity,
                          init_nothing,
                          &dynamic_ft.entries);
  if (!happy) rte_exit(EXIT_FAILURE, "error allocating dynamic array");

#ifdef KLEE_VERIFICATION
  map_set_layout(dynamic_ft.map, dynamic_map_key_fields,
                 sizeof(dynamic_map_key_fields)/sizeof(dynamic_map_key_fields[0]));
  vector_set_layout(dynamic_ft.entries, dynamic_vector_entry_fields,
                    sizeof(dynamic_vector_entry_fields)/
                    sizeof(dynamic_vector_entry_fields[0]));
#endif//KLEE_VERIFICATION
}

int nf_core_process(uint8_t device,
                    struct rte_mbuf* mbuf,
                    uint32_t now) {
  struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

  bridge_expire_entries(now);
  bridge_put_update_entry(&ether_header->s_addr, device, now);

  int dst_device = bridge_get_device(&ether_header->d_addr,
                                     device);

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
  bridge_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  bridge_config_cmdline_print_usage();
}

void nf_print_config() {
  bridge_print_config(&config);
}

#ifdef KLEE_VERIFICATION

void nf_loop_iteration_begin(unsigned lcore_id,
                             uint32_t time) {
  rte_reset();
  dchain_reset(dynamic_ft.heap, config.dyn_capacity);
  /* map_reset(dynamic_ft.map); */
  /* vector_reset(dynamic_ft.entries); */
  /* map_reset(static_ft.map); */
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       uint32_t time) {
  rte_reset();
  dchain_reset(dynamic_ft.heap, config.dyn_capacity);
  map_reset(dynamic_ft.map);
  vector_reset(dynamic_ft.entries);
  map_reset(static_ft.map);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           uint32_t time) {
}

#endif//KLEE_VERIFICATION
