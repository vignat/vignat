#include <string.h>
#include "bridge_data.h"

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

void init_nothing(void* entry) {
  /* do nothing */
}

void init_nothing_st(void* entry) {
  /* do nothing */
}

void dyn_entry_get_addr(void* entry,
                        void** addr_out) {
  *((struct ether_addr**)addr_out) = &((struct DynamicEntry*)entry)->addr;
}

void dyn_entry_retrieve_addr(void* entry, void* addr) {
  /* do nothing */
}
