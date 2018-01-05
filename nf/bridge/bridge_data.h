#ifndef _BRIDGE_DATA_H_INCLUDED_
#define _BRIDGE_DATA_H_INCLUDED_

#include "stdbool.h"

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

  predicate ether_addrp(struct ether_addr* ptr; ether_addri addr) =
    struct_ether_addr_padding(ptr) &*&
    ptr->a |-> ?a &*&
    ptr->b |-> ?b &*&
    ptr->c |-> ?c &*&
    ptr->d |-> ?d &*&
    ptr->e |-> ?e &*&
    ptr->f |-> ?f &*&
    addr == eaddrc(a, b, c, d, e, f);

  predicate static_keyp(struct StaticKey* ptr; stat_keyi k) =
    struct_StaticKey_padding(ptr) &*&
    ptr->device |-> ?device &*&
    ether_addrp(&ptr->addr, ?addr) &*&
    k == stkc(device, addr);

  predicate dynamic_entryp(struct DynamicEntry* ptr; dynenti de) =
    struct_DynamicEntry_padding(ptr) &*&
    ptr->device |-> ?device &*&
    ether_addrp(&ptr->addr, ?addr) &*&
    de == dynentc(device, addr);

  predicate dynamic_entry_barep(struct DynamicEntry* ptr, dynenti de) =
    struct_DynamicEntry_padding(ptr) &*&
    switch(de) { case dynentc(device,addr):
      return ptr->device |-> device;
    };

  fixpoint bool dynentry_right_offsets(void* ptr, void* eaddr);
  fixpoint ether_addri dynentry_get_addr_fp(dynenti de);

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

void dyn_entry_get_addr(void* entry,
                        void** addr_out);
/*@ requires [?fr]dynamic_entryp(entry, ?de) &*&
             *addr_out |-> _; @*/
/*@ ensures [fr]dynamic_entry_barep(entry, de) &*&
            *addr_out |-> ?ao &*&
            [fr]ether_addrp(ao, dynentry_get_addr_fp(de)) &*&
            true == dynentry_right_offsets(entry, ao); @*/

void dyn_entry_retrieve_addr(void* entry, void* addr);
/*@ requires [?fr]dynamic_entry_barep(entry, ?de) &*&
             [fr]ether_addrp(addr, dynentry_get_addr_fp(de)) &*&
             true == dynentry_right_offsets(entry, addr); @*/
/*@ ensures [fr]dynamic_entryp(entry, de); @*/

void init_nothing(void* entry);
/*@ requires chars(entry, sizeof(struct DynamicEntry), _); @*/
/*@ ensures dynamic_entryp(entry, _); @*/

void init_nothing_st(void* entry);
/*@ requires chars(entry, sizeof(struct StaticKey), _); @*/
/*@ ensures static_keyp(entry, _); @*/

#endif//_BRIDGE_DATA_H_INCLUDED_
