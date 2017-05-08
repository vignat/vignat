#include <stdlib.h>
#include "lib/containers/map-impl.h"
#include "map.h"

struct Map {
  int* busybits;
  void** keyps;
  int* khs;
  int* chns;
  int* vals;
  int capacity;
  int size;
  map_keys_equality* keys_eq;
  map_key_hash* khash;
};

#ifndef NULL
#define NULL 0
#endif//NULL

/*@
  predicate mapp<t>(struct Map* ptr,
                    predicate (void*;t) kp,
                    fixpoint (t,int) hsh,
                    fixpoint (t,int,bool) recp,
                    mapi<t> map) =
    malloc_block_Map(ptr) &*&
    ptr->busybits |-> ?busybits &*&
    ptr->keyps |-> ?keyps &*&
    ptr->khs |-> ?khs &*&
    ptr->chns |-> ?chns &*&
    ptr->vals |-> ?vals &*&
    ptr->capacity |-> ?capacity &*&
    ptr->size |-> ?size &*&
    ptr->keys_eq |-> ?keys_eq &*&
    ptr->khash |-> ?khash &*&
    malloc_block_ints(busybits, capacity) &*&
    malloc_block_pointers(keyps, capacity) &*&
    malloc_block_ints(khs, capacity) &*&
    malloc_block_ints(chns, capacity) &*&
    malloc_block_ints(vals, capacity) &*&
    [_]is_map_keys_equality<t>(keys_eq, kp) &*&
    [_]is_map_key_hash<t>(khash, kp, hsh) &*&
    mapping(?m, ?addrs, kp, recp, hsh, capacity,
            busybits, keyps, khs, chns, vals) &*&
    size == length(m) &*&
    map == mapc(capacity, m, addrs);
  @*/

int map_allocate/*@ <t> @*/(map_keys_equality* keq, map_key_hash* khash,
                            int capacity,
                            struct Map** map_out)
/*@ requires 0 < capacity &*& capacity < CAPACITY_UPPER_LIMIT &*&
             [_]is_map_keys_equality<t>(keq, ?kp) &*&
             [_]is_map_key_hash<t>(khash, kp, ?hsh) &*&
             *map_out |-> ?old_mo; @*/
/*@ ensures result == 0 ?
              *map_out |-> old_mo :
              (*map_out |-> ?new_mo &*&
               result == 1 &*&
               mapp<t>(new_mo, kp, hsh, nop_true,
                       mapc(capacity, nil, nil))); @*/
{
  struct Map* old_map_val = *map_out;
  struct Map* map_alloc = malloc(sizeof(struct Map));
  if (map_alloc == NULL) return 0;
  *map_out = (struct Map*) map_alloc;
  int* bbs_alloc = malloc(sizeof(int)*capacity);
  if (bbs_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->busybits = bbs_alloc;
  void** keyps_alloc = malloc(sizeof(void*)*capacity);
  if (keyps_alloc == NULL) {
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->keyps = keyps_alloc;
  int* khs_alloc = malloc(sizeof(int)*capacity);
  if (khs_alloc == NULL) {
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs = khs_alloc;
  int* chns_alloc = malloc(sizeof(int)*capacity);
  if (chns_alloc == NULL) {
    free(khs_alloc);
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->chns = chns_alloc;
  int* vals_alloc = malloc(sizeof(int)*capacity);
  if (vals_alloc == NULL) {
    free(chns_alloc);
    free(khs_alloc);
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->vals = vals_alloc;
  (*map_out)->capacity = capacity;
  (*map_out)->size = 0;
  (*map_out)->keys_eq = keq;
  (*map_out)->khash = khash;
  //@ close map_key_type<t>();
  //@ close map_key_hash<t>(hsh);
  //@ close map_record_property<t>(nop_true);
  map_impl_init((*map_out)->busybits,
                keq,
                (*map_out)->keyps,
                (*map_out)->khs,
                (*map_out)->chns,
                (*map_out)->vals,
                capacity);
  /*@
    close mapp<t>(*map_out, kp, hsh, nop_true, mapc(capacity, nil, nil));
    @*/
  return 1;
}

int map_get/*@ <t> @*/(struct Map* map, void* key, int* value_out)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             kp(key, ?k) &*&
             *value_out |-> ?old_v; @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, contents, addrs)) &*&
            kp(key, k) &*&
            map_has_fp(contents, k) ?
              (result == 1 &*&
               *value_out |-> ?new_v &*&
               new_v == map_get_fp(contents, k)) :
              (result == 0 &*&
               *value_out |-> old_v); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  map_key_hash* khash = map->khash;
  int hash = khash(key);
  return map_impl_get(map->busybits,
                      map->keyps,
                      map->khs,
                      map->chns,
                      map->vals,
                      key,
                      map->keys_eq,
                      hash,
                      value_out,
                      map->capacity);
  //@ close mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
}

void map_put/*@ <t> @*/(struct Map* map, void* key, int value)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             [0.5]kp(key, ?k) &*&
             true == recp(k, value) &*&
             length(contents) < capacity &*&
             false == map_has_fp(contents, k); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, map_put_fp(contents, k, value),
                         map_put_fp(addrs, k, key))); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  map_key_hash* khash = map->khash;
  int hash = khash(key);
  map_impl_put(map->busybits,
               map->keyps,
               map->khs,
               map->chns,
               map->vals,
               key, hash, value,
               map->capacity);
  ++map->size;
  /*@ close mapp<t>(map, kp, hsh, recp, mapc(capacity,
                                             map_put_fp(contents, k, value),
                                             map_put_fp(addrs, k, key)));
  @*/
}

/*@
  lemma void map_erase_decrement_len<kt, vt>(list<pair<kt, vt> > m, kt k)
  requires true == map_has_fp(m, k);
  ensures length(m) == 1 + length(map_erase_fp(m, k));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,val):
          if (key != k) map_erase_decrement_len(t, k);
        }
    }
  }
  @*/

/*@
  lemma void map_get_mem<t>(list<pair<t, int> > m, t k)
  requires true == map_has_fp(m, k);
  ensures true == mem(pair(k, map_get_fp(m, k)), m);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, val):
          if (key != k) map_get_mem(t, k);
        }
    }
  }
  @*/

void map_erase/*@ <t> @*/(struct Map* map, void* key, void** trash)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             [0.5]kp(key, ?k) &*&
             *trash |-> _ &*&
             true == map_has_fp(contents, k); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, map_erase_fp(contents, k),
                         map_erase_fp(addrs, k))) &*&
            [0.5]kp(key, k) &*&
            *trash |-> ?k_out &*&
            [0.5]kp(k_out, k); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  map_key_hash* khash = map->khash;
  int hash = khash(key);
  map_impl_erase(map->busybits,
                 map->keyps,
                 map->khs,
                 map->chns,
                 key,
                 map->keys_eq,
                 hash,
                 map->capacity,
                 trash);
  --map->size;
  //@ map_erase_decrement_len(contents, k);
  /*@
    close mapp<t>(map, kp, hsh, recp, mapc(capacity,
                                           map_erase_fp(contents, k),
                                           map_erase_fp(addrs, k)));
    @*/
}

int map_size/*@ <t> @*/(struct Map* map)
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, contents, addrs)) &*&
            result == length(contents); @*/
{
  //@ open mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
  return map->size;
  //@ close mapp<t>(map, kp, hsh, recp, mapc(capacity, contents, addrs));
}
