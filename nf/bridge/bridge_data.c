#include <string.h>
#include "bridge_data.h"

bool ether_addr_eq(void* k1, void* k2)
/*@ requires [?fr1]ether_addrp(k1, ?ea1) &*&
             [?fr2]ether_addrp(k2, ?ea2); @*/
/*@ ensures [fr1]ether_addrp(k1, ea1) &*&
            [fr2]ether_addrp(k2, ea2) &*&
            (result ? (ea1 != ea2) : ea1 == ea2); @*/
{
  struct ether_addr* a = (struct ether_addr*)k1;
  struct ether_addr* b = (struct ether_addr*)k2;
  return 0 == memcmp(a,
                     b,
                     sizeof(struct ether_addr));
}

bool static_key_eq(void* k1, void* k2)
/*@ requires [?fr1]static_keyp(k1, ?sk1) &*&
             [?fr2]static_keyp(k2, ?sk2); @*/
/*@ ensures [fr1]static_keyp(k1, sk1) &*&
            [fr2]static_keyp(k2, sk2) &*&
            (result ? (sk1 != sk2) : sk1 == sk2); @*/
{
  struct StaticKey* a = (struct StaticKey*) k1;
  struct StaticKey* b = (struct StaticKey*) k2;
  return a->device == b->device && ether_addr_eq(&a->addr, &b->addr);

}

int ether_addr_hash(void* k)
/*@ requires [?fr]ether_addrp(k, ?ea); @*/
/*@ ensures [fr]ether_addrp(k, ea) &*&
            result == eth_addr_hash(ea); @*/
{
  struct ether_addr* addr = (struct ether_addr*)k;
  return (int)((*(uint32_t*)addr) ^
               (*(uint32_t*)((char*)addr + 2)));
}

int static_key_hash(void* key)
/*@ requires chars(entry, sizeof(struct ether_addr), _); @*/
/*@ ensures ether_addrp(entry, _); @*/
{
  struct StaticKey *k = (struct StaticKey*)key;
  return (ether_addr_hash(&k->addr) << 2) ^ k->device;
}

void init_nothing_ea(void* entry)
/*@ requires chars(entry, sizeof(struct ether_addr), _); @*/
/*@ ensures ether_addrp(entry, _); @*/
{
  /* do nothing */
}

void init_nothing_dv(void* entry)
/*@ requires chars(entry, sizeof(struct DynamicValue), _); @*/
/*@ ensures dyn_valp(entry, _); @*/
{
  /* do nothing */
}

void init_nothing_st(void* entry)
/*@ requires chars(entry, sizeof(struct StaticKey), _); @*/
/*@ ensures static_keyp(entry, _); @*/
{
  /* do nothing */
}
