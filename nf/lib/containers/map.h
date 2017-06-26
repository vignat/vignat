#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

#include "map-impl.h"
#include "map-util.h"

struct Map;

/*@
  inductive mapi<t> = mapc(int, list<pair<t, int> >,
                           list<pair<t, void*> >);

  predicate mapp<t>(struct Map* ptr,
                    predicate (void*;t) kp,
                    fixpoint (t,int) hsh,
                    fixpoint (t,int,bool) recp,
                    mapi<t> map);

  fixpoint bool nop_true<t>(t key, int val) { return true; }
  @*/

/*@
  lemma void map_get_mem<t>(list<pair<t, int> > m, t k);
  requires true == map_has_fp(m, k);
  ensures true == mem(pair(k, map_get_fp(m, k)), m);
  @*/

int map_allocate/*@ <t> @*/(map_keys_equality* keq,
                            map_key_hash* khash, int capacity,
                            struct Map** map_out);
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

int map_get/*@ <t> @*/(struct Map* map, void* key, int* value_out);
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

void map_put/*@ <t> @*/(struct Map* map, void* key, int value);
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)) &*&
             [0.5]kp(key, ?k) &*&
             true == recp(k, value) &*&
             length(contents) < capacity &*&
             false == map_has_fp(contents, k); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, map_put_fp(contents, k, value),
                         map_put_fp(addrs, k, key))); @*/

void map_erase/*@ <t> @*/(struct Map* map, void* key, void** trash);
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

int map_size/*@ <t> @*/(struct Map* map);
/*@ requires mapp<t>(map, ?kp, ?hsh, ?recp,
                     mapc(?capacity, ?contents, ?addrs)); @*/
/*@ ensures mapp<t>(map, kp, hsh, recp,
                    mapc(capacity, contents, addrs)) &*&
            result == length(contents); @*/

#endif//_MAP_H_INCLUDED_
