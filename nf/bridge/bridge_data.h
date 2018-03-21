#ifndef _BRIDGE_DATA_H_INCLUDED_
#define _BRIDGE_DATA_H_INCLUDED_

#include "stdbool.h"

#include "rte_ether.h"

#include "lib/stubs/core_stub.h"

struct Map;
struct Vector;
struct DoubleChain;

struct StaticKey {
  struct ether_addr addr;
  uint16_t device;
};

struct DynamicValue {
  uint16_t device;
};

struct DynamicFilterTable {
  struct Map* map;
  struct DoubleChain* heap;
  struct Vector* keys;
  struct Vector* values;
};

struct StaticFilterTable {
  struct Map* map;
  struct Vector* keys;
};

/*@
  inductive stat_keyi = stkc(int, ether_addri);
  predicate static_keyp(struct StaticKey* ptr; stat_keyi k) =
    struct_StaticKey_padding(ptr) &*&
    ptr->device |-> ?device &*&
    ether_addrp(&ptr->addr, ?addr) &*&
    k == stkc(device, addr);

  predicate dyn_valp(struct DynamicValue *ptr; uint16_t dev) =
    struct_DynamicValue_padding(ptr) &*&
    ptr->device |-> dev;

  fixpoint bool dynentry_right_offsets(void* ptr, void* eaddr);

  fixpoint int eth_addr_hash(ether_addri ea);

  fixpoint int st_key_hash(stat_keyi k);
  @*/


bool ether_addr_eq(void* k1, void* k2);
/*@ requires [?fr1]ether_addrp(k1, ?ea1) &*&
             [?fr2]ether_addrp(k2, ?ea2); @*/
/*@ ensures [fr1]ether_addrp(k1, ea1) &*&
            [fr2]ether_addrp(k2, ea2) &*&
            (result == false ? (ea1 != ea2) : ea1 == ea2); @*/

bool static_key_eq(void* k1, void* k2);
/*@ requires [?fr1]static_keyp(k1, ?sk1) &*&
             [?fr2]static_keyp(k2, ?sk2); @*/
/*@ ensures [fr1]static_keyp(k1, sk1) &*&
            [fr2]static_keyp(k2, sk2) &*&
            (result == false ? (sk1 != sk2) : sk1 == sk2); @*/


int ether_addr_hash(void* k);
/*@ requires [?fr]ether_addrp(k, ?ea); @*/
/*@ ensures [fr]ether_addrp(k, ea) &*&
            result == eth_addr_hash(ea); @*/

int static_key_hash(void* key);
/*@ requires [?fr]static_keyp(key, ?sk); @*/
/*@ ensures [fr]static_keyp(key, sk) &*&
            result == st_key_hash(sk); @*/

void init_nothing_ea(void* entry);
/*@ requires chars(entry, sizeof(struct ether_addr), _); @*/
/*@ ensures ether_addrp(entry, _); @*/

void init_nothing_dv(void* entry);
/*@ requires chars(entry, sizeof(struct DynamicValue), _); @*/
/*@ ensures dyn_valp(entry, _); @*/


void init_nothing_st(void* entry);
/*@ requires chars(entry, sizeof(struct StaticKey), _); @*/
/*@ ensures static_keyp(entry, _); @*/

#endif//_BRIDGE_DATA_H_INCLUDED_
