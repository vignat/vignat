#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

#include "map-impl.h"
#include "map-util.h"

struct Map;

/*@
  inductive mapi<t> = mapc(int, list<pair<t, int> >);

  predicate mapp<t>(struct Map* ptr,
                    predicate (void*;t) kp,
                    fixpoint (t,int) hsh;
                    mapi<t> map);
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
               mapp(new_mo, kp, hsh, mapc(capacity, nil))); @*/

int map_get/*@ <t> @*/(struct Map* map, void* key, int* value_out);
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)) &*&
             kp(key, ?k) &*&
             *value_out |-> ?old_v; @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, contents)) &*&
            kp(key, k) &*&
            map_has_fp(contents, k) ?
              (result == 1 &*&
               *value_out |-> ?new_v &*&
               new_v == map_get_fp(contents, k)) :
              (result == 0 &*&
               *value_out |-> old_v); @*/

void map_put/*@ <t> @*/(struct Map* map, void* key, int value);
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)) &*&
             [0.5]kp(key, ?k) &*&
             length(contents) < capacity &*&
             false == map_has_fp(contents, k); @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, map_put_fp(contents, k, value))); @*/

void map_erase/*@ <t> @*/(struct Map* map, void* key, void** trash);
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)) &*&
             [0.5]kp(key, ?k) &*&
             *trash |-> _ &*&
             true == map_has_fp(contents, k); @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, map_erase_fp(contents, k))) &*&
            [0.5]kp(key, k) &*&
            *trash |-> ?k_out &*&
            [0.5]kp(k_out, k); @*/

int map_size/*@ <t> @*/(struct Map* map);
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)); @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, contents)) &*&
            result == length(contents); @*/

#endif//_MAP_H_INCLUDED_
