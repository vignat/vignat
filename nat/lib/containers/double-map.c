#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "double-map.h"

struct DoubleMap {
  int value_size;

  uq_value_copy* cpy;

  uint8_t *values;

  int *bbs_a;
  void **kps_a;
  int *khs_a;
  int *inds_a;
  map_keys_equality *eq_a;
  map_key_hash *hsh_a;

  int *bbs_b;
  void **kps_b;
  int *khs_b;
  int *inds_b;
  map_keys_equality *eq_b;
  map_key_hash *hsh_b;
  dmap_extract_keys *exk;
  dmap_pack_keys *pk;

  int n_vals;
  int capacity;
};

int dmap_allocate/*@ <K1,K2,V> @*/
                 (map_keys_equality* eq_a, map_key_hash* hsh_a,
                  map_keys_equality* eq_b, map_key_hash* hsh_b,
                  int value_size, uq_value_copy* v_cpy,
                  dmap_extract_keys* dexk,
                  dmap_pack_keys* dpk,
                  int capacity,
                  struct DoubleMap** map_out)
/*@ requires exists<pair<pair<K1,K2>,V > >(pair(pair(_, _), _)) &*&
             [_]is_map_keys_equality<K1>(eq_a, ?keyp1) &*&
             [_]is_map_key_hash<K1>(hsh_a, keyp1, ?hsh1) &*&
             [_]is_map_keys_equality<K2>(eq_b, ?keyp2) &*&
             [_]is_map_key_hash<K2>(hsh_b, keyp2, ?hsh2) &*&
             [_]is_uq_value_copy<V>(v_cpy, ?fvp, value_size) &*&
             [_]is_dmap_extract_keys(dexk, keyp1, keyp2, fvp,
                                     ?bvp, ?rof, ?vk1, ?vk2) &*&
             [_]is_dmap_pack_keys(dpk, keyp1, keyp2, fvp, bvp, rof, vk1, vk2) &*&
             exists<fixpoint(K1,K2,V,int,bool)>(?recp) &*&
             *map_out |-> ?old_map_out &*&
             0 < value_size; @*/
/*@ ensures result == 0 ?
            (*map_out |-> old_map_out) :
            (*map_out |-> ?mapp &*&
             result == 1 &*&
             dmappingp<K1,K2,V>(empty_dmap_fp(), keyp1,
                                keyp2, hsh1, hsh2, fvp, bvp, rof, value_size,
                                vk1, vk2, recp,
                                capacity, mapp)); @*/
{
  if (NULL == (*map_out = malloc(sizeof(struct DoubleMap)))) return 0;

  (**map_out).eq_a = eq_a;
  (**map_out).hsh_a = hsh_a;
  (**map_out).eq_b = eq_b;
  (**map_out).hsh_b = hsh_b;
  (**map_out).value_size = value_size;
  (**map_out).cpy = v_cpy;
  (**map_out).exk = dexk;
  (**map_out).pk = dpk;
  (**map_out).capacity = capacity;

  if (NULL == ((**map_out).values = malloc(value_size   *capacity))) return 0;
  if (NULL == ((**map_out).bbs_a  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == ((**map_out).kps_a  = malloc(sizeof(void*)*capacity))) return 0;
  if (NULL == ((**map_out).khs_a  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == ((**map_out).inds_a = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == ((**map_out).bbs_b  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == ((**map_out).kps_b  = malloc(sizeof(void*)*capacity))) return 0;
  if (NULL == ((**map_out).khs_b  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == ((**map_out).inds_b = malloc(sizeof(int)  *capacity))) return 0;

  map_initialize((**map_out).bbs_a, (**map_out).eq_a,
                 (**map_out).kps_a, (**map_out).khs_a, (**map_out).inds_a,
                 (**map_out).capacity);
  map_initialize((**map_out).bbs_b, (**map_out).eq_b,
                 (**map_out).kps_b, (**map_out).khs_b, (**map_out).inds_b,
                 (**map_out).capacity);

  (**map_out).n_vals = 0;
  return 1;
}

int dmap_get_a/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp, ?cap, map) &*&
             kp1(key, ?k1) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp, cap, map) &*&
            kp1(key, k1) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k1_fp(m, k1) &*&
              true == rp(k1, dmap_get_k2_by_idx_fp(m,ind),
                         dmap_get_val_fp(m,ind), ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  return map_get(map->bbs_a, map->kps_a, map->khs_a, map->inds_a, key,
                 map->eq_a, map->hsh_a(key), index,
                 map->capacity);
}

int dmap_get_b/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp, ?cap, map) &*&
             kp2(key, ?k2) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp, cap, map) &*&
            kp2(key, k2) &*&
            (dmap_has_k2_fp(m, k2) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k2_fp(m, k2) &*&
              true == rp(dmap_get_k1_by_idx_fp(m,ind),
                         k2, dmap_get_val_fp(m, ind), ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  return map_get(map->bbs_b, map->kps_b, map->khs_b, map->inds_b, key,
                 map->eq_b, map->hsh_b(key), index,
                 map->capacity);
}

int dmap_put/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* value, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp, ?cap, map) &*&
             fvp(value, ?v) &*& true == rp(vk1(v), vk2(v), v, index) &*&
             false == dmap_index_used_fp(m, index) &*&
             false == dmap_has_k1_fp(m, vk1(v)) &*&
             false == dmap_has_k2_fp(m, vk2(v)); @*/
/*@ ensures (dmap_size_fp(m) < cap ?
             (result == 1 &*&
              dmappingp<K1,K2,V>(dmap_put_fp(m, vk1(v), vk2(v), index, v),
                                 kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp, cap, map))) &*&
            fvp(value, v);@*/
{
  void* my_value = map->values + index*map->value_size;
  map->cpy(my_value, value);
  void* key_a = 0;
  void* key_b = 0;
  map->exk(my_value, &key_a, &key_b);
  int ret = map_put(map->bbs_a, map->kps_a, map->khs_a,
                    map->inds_a, key_a,
                    map->hsh_a(key_a),
                    index, map->capacity) &&
    map_put(map->bbs_b, map->kps_b, map->khs_b,
            map->inds_b, key_b,
            map->hsh_b(key_b),
            index, map->capacity);
  if (ret) ++map->n_vals;
  return ret;
}

void dmap_get_value/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index,
                                     char* value_out)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             value_out[0..vsz] |-> _; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp, cap, map) &*&
            fvp(value_out, dmap_get_val_fp(m, index)); @*/
{
  map->cpy(value_out, map->values + index*map->value_size);
}

int dmap_erase/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true; @*/ //Should also require memory access here
/*@ ensures (dmap_index_used_fp(m, index) ?
             (result == 1 &*&
              dmappingp<K1,K2,V>(dmap_erase_fp(m, index),
                                 kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp, cap, map))) &*&
              fvp(_, dmap_get_val_fp(m, index)); @*/
{
  void* key_a = 0;
  void* key_b = 0;
  map->exk(map->values + index*map->value_size, &key_a, &key_b);
  int ret = map_erase(map->bbs_a, map->kps_a, map->khs_a, key_a,
                      map->eq_a, map->hsh_a(key_a),
                      map->capacity) &&
    map_erase(map->bbs_b, map->kps_b, map->khs_b, key_b,
              map->eq_b, map->hsh_b(key_b),
              map->capacity);
  if (ret) --map->n_vals;
  return ret;
}

int dmap_size/*@ <K1,K2,V> @*/(struct DoubleMap* map)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp, ?cap, map); @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp, cap, map) &*&
            result == dmap_size_fp(m); @*/
{
  return map->n_vals;
}

