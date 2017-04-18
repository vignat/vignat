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
               mapp(new_mo, kp, hsh, mapc(capacity, nil))); @*/
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
  map_impl_init((*map_out)->busybits,
                keq,
                (*map_out)->keyps,
                (*map_out)->khs,
                (*map_out)->chns,
                (*map_out)->vals,
                capacity);
  return 1;
}

int map_get/*@ <t> @*/(struct Map* map, void* key, int* value_out)
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
{
  int hash = map->khash(key);
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
}

void map_put/*@ <t> @*/(struct Map* map, void* key, int value)
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)) &*&
             [0.5]kp(key, ?k) &*&
             length(contents) < capacity &*&
             false == map_has_fp(contents, k); @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, map_put_fp(contents, k, value))); @*/
{
  int hash = map->khash(key);
  map_impl_put(map->busybits,
               map->keyps,
               map->khs,
               map->chns,
               map->vals,
               key, hash, value,
               map->capacity);
  ++map->size;
}

void map_erase/*@ <t> @*/(struct Map* map, void* key, void** trash)
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)) &*&
             [0.5]kp(key, ?k) &*&
             *trash |-> _ &*&
             true == map_has_fp(contents, k); @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, map_erase_fp(contents, k))) &*&
            [0.5]kp(key, k) &*&
            *trash |-> ?k_out &*&
            [0.5]kp(k_out, k); @*/
{
  int hash = map->khash(key);
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
}

int map_size/*@ <t> @*/(struct Map* map)
/*@ requires mapp(map, ?kp, ?hsh, mapc(?capacity, ?contents)); @*/
/*@ ensures mapp(map, kp, hsh, mapc(capacity, contents)) &*&
            result == length(contents); @*/
{
  return map->size;
}
