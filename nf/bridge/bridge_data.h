#ifndef _BRIDGE_DATA_H_INCLUDED_
#define _BRIDGE_DATA_H_INCLUDED_

#include "lib/custom_ether_addr_def.h"

struct Map;
struct Vector;
struct DoubleChain;

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

/*@
  inductive ether_addri = eaddrc(int, int, int, int, int, int);
  inductive stat_keyi = stkc(int, ether_addri);
  inductive dynenti = dynentc(int, ether_addri);

  predicate ether_addrp(void* ptr; ether_addri addr);
  predicate static_keyp(void* ptr; stat_keyi k);
  predicate dynamic_entryp(void* ptr; dynenti de);

  fixpoint int ether_addr_hash(ether_addri ea);

  fixpoint int st_key_hash(stat_keyi k);
  @*/


int ether_addr_eq(void* k1, void* k2);
/*@ requires [?fr1]ether_addrp(k1, ?ea1) &*&
             [?fr2]ether_addrp(k2, ?ea2); @*/
/*@ ensures [fr1]ether_addrp(k1, ea1) &*&
            [fr2]ether_addrp(k2, ea2) &*&
            (result == 0 ? (ea1 != ea2) : ea1 == ea2); @*/

int static_key_eq(void* k1, void* k2);
/*@ requires [?fr1]static_keyp(k1, ?sk1) &*&
             [?fr2]static_keyp(k2, ?sk2); @*/
/*@ ensures [fr1]static_keyp(k1, sk1) &*&
            [fr2]static_keyp(k2, sk2) &*&
            (result == 0 ? (sk1 != sk2) : sk1 == sk2); @*/


int ether_addr_hash(void* k);
/*@ requires [?fr]ether_addrp(k, ?ea); @*/
/*@ ensures [fr]ether_addrp(k, ea) &*&
            result == ether_addr_hash(ea); @*/

int static_key_hash(void* key);
/*@ requires [?fr]static_keyp(key, ?sk); @*/
/*@ ensures [fr]static_keyp(key, sk) &*&
            result == st_key_hash(sk); @*/

void dyn_entry_get_addr(void* entry,
                        void** addr_out);
/*@ requires true; @*/
/*@ ensures true; @*/

void dyn_entry_retrieve_addr(void* entry, void* addr);
/*@ requires true; @*/
/*@ ensures true; @*/

void init_nothing(void* entry);
/*@ requires chars(entry, sizeof(struct DynamicEntry), _); @*/
/*@ ensures dynamic_entryp(entry, _); @*/

#endif//_BRIDGE_DATA_H_INCLUDED_
