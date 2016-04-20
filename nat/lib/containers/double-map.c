#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "double-map.h"

//@ #include "arith.gh"

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

/*@
  fixpoint bool part_recp1<t1,t2,vt>(dmap<t1,t2,vt> m, fixpoint (t1,t2,vt,int,bool) recp,
                                     t1 k1, int ind) {
    return recp(k1, dmap_get_k2_by_idx_fp(m, ind),
                dmap_get_val_fp(m, ind), ind);
  }

  fixpoint bool part_recp2<t1,t2,vt>(dmap<t1,t2,vt> m, fixpoint (t1,t2,vt,int,bool) recp,
                                     t2 k2, int ind) {
    return recp(dmap_get_k1_by_idx_fp(m, ind), k2,
                dmap_get_val_fp(m, ind), ind);
  }

  predicate dmappingp<t1,t2,vt>(dmap<t1,t2,vt> m,
                                predicate (void*;t1) keyp1,
                                predicate (void*;t2) keyp2,
                                fixpoint (t1,int) hsh1,
                                fixpoint (t2,int) hsh2,
                                predicate (void*,vt) full_vp,
                                predicate (void*,vt) bare_vp,
                                fixpoint (void*,void*,void*,bool) right_offsets,
                                int val_size,
                                fixpoint (vt,t1) vk1,
                                fixpoint (vt,t2) vk2,
                                fixpoint (t1,t2,vt,int,bool) recp,
                                int capacity,
                                struct DoubleMap* mp) =
    mp->value_size |-> val_size &*&
    mp->cpy |-> ?v_cpy &*&
    [_]is_uq_value_copy<vt>(v_cpy, full_vp, val_size) &*&
    mp->values |-> ?values &*&
    values[0..(val_size*capacity)] |-> _ &*&
    mp->bbs_a |-> ?bbs_a &*&
    mp->kps_a |-> ?kps_a &*&
    mp->khs_a |-> ?khs_a &*&
    mp->inds_a |-> ?inds_a &*&
    mapping(?ma, keyp1, (part_recp1)(m, recp), hsh1, capacity,
            bbs_a, kps_a, khs_a, inds_a) &*&
    mp->eq_a |-> ?eq_a &*&
    [_]is_map_keys_equality<t1>(eq_a, keyp1) &*&
    mp->hsh_a |-> ?hsh_a &*&
    [_]is_map_key_hash<t1>(hsh_a, keyp1, hsh1) &*&
    mp->bbs_b |-> ?bbs_b &*&
    mp->kps_b |-> ?kps_b &*&
    mp->khs_b |-> ?khs_b &*&
    mp->inds_b |-> ?inds_b &*&
    mapping(?mb, keyp2, (part_recp2)(m, recp), hsh2, capacity,
            bbs_b, kps_b, khs_b, inds_b) &*&
    mp->eq_b |-> ?eq_b &*&
    [_]is_map_keys_equality<t2>(eq_b, keyp2) &*&
    mp->hsh_b |-> ?hsh_b &*&
    [_]is_map_key_hash<t2>(hsh_b, keyp2, hsh2) &*&
    mp->exk |-> ?exk &*&
    [_]is_dmap_extract_keys(exk, keyp1, keyp2, full_vp, bare_vp,
                            right_offsets, vk1, vk2) &*&
    mp->pk |-> ?pk &*&
    [_]is_dmap_pack_keys(pk, keyp1, keyp2, full_vp, bare_vp,
                         right_offsets, vk1, vk2);
  @*/

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
             0 < value_size &*& value_size < 4096 &*&
             0 < capacity &*& capacity < 4096; @*/
/*@ ensures result == 0 ?
            (*map_out |-> old_map_out) :
            (*map_out |-> ?mapp &*&
             result == 1 &*&
             dmappingp<K1,K2,V>(empty_dmap_fp(), keyp1,
                                keyp2, hsh1, hsh2, fvp, bvp, rof, value_size,
                                vk1, vk2, recp,
                                capacity, mapp)); @*/
{
  //@ open exists<fixpoint(K1,K2,V,int,bool)>(_);
  //@ open exists(pair(pair(?k1_null, ?k2_null), ?v_null));
  struct DoubleMap* old_map_val = *map_out;
  struct DoubleMap* map_alloc = malloc(sizeof(struct DoubleMap));
  if (map_alloc == NULL) return 0;
  *map_out = (struct DoubleMap*) map_alloc;

  //@ mul_bounds(value_size, 4096, capacity, 4096);
  uint8_t* vals_alloc = malloc(value_size   *capacity);
  if (vals_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->values = vals_alloc;
  int* bbs_a_alloc = malloc(sizeof(int)  *capacity);
  if (bbs_a_alloc == NULL) {
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_a = bbs_a_alloc;
  void** kps_a_alloc = malloc(sizeof(void*)  *capacity);
  if (kps_a_alloc == NULL) {
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_a = kps_a_alloc;
  int* khs_a_alloc = malloc(sizeof(int)  *capacity);
  if (khs_a_alloc == NULL) {
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_a = khs_a_alloc;
  int* inds_a_alloc = malloc(sizeof(int)  *capacity);
  if (inds_a_alloc == NULL) {
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->inds_a = inds_a_alloc;
  int* bbs_b_alloc = malloc(sizeof(int)  *capacity);
  if (bbs_b_alloc == NULL) {
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_b = bbs_b_alloc;
  void** kps_b_alloc = malloc(sizeof(void*)  *capacity);
  if (kps_b_alloc == NULL) {
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_b = kps_b_alloc;
  int* khs_b_alloc = malloc(sizeof(int)  *capacity);
  if (khs_b_alloc == NULL) {
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_b = khs_b_alloc;
  int* inds_b_alloc = malloc(sizeof(int)  *capacity);
  if (inds_b_alloc == NULL) {
    free(khs_b_alloc);
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->inds_b = inds_b_alloc;

  (*map_out)->eq_a = eq_a;
  (*map_out)->hsh_a = hsh_a;
  (*map_out)->eq_b = eq_b;
  (*map_out)->hsh_b = hsh_b;
  (*map_out)->value_size = value_size;
  (*map_out)->cpy = v_cpy;
  (*map_out)->exk = dexk;
  (*map_out)->pk = dpk;
  (*map_out)->capacity = capacity;

  //@ assume(false); //<-- see verifast#22
  //@ close exists(pair(k1_null,hsh1));
  map_initialize((*map_out)->bbs_a, (*map_out)->eq_a,
                 (*map_out)->kps_a, (*map_out)->khs_a, (*map_out)->inds_a,
                 (*map_out)->capacity);
  //@ close exists(pair(k2_null,hsh2));
  map_initialize((*map_out)->bbs_b, (*map_out)->eq_b,
                 (*map_out)->kps_b, (*map_out)->khs_b, (*map_out)->inds_b,
                 (*map_out)->capacity);

  (*map_out)->n_vals = 0;
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
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp, cap, map); @*/
  map_key_hash *hsh_a = map->hsh_a;
  //@ assert([_]is_map_key_hash<K1>(hsh_a, _, _));
  int hash = hsh_a(key);
  int rez = map_get(map->bbs_a, map->kps_a, map->khs_a, map->inds_a, key,
                    map->eq_a, hash, index,
                    map->capacity);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp, cap, map); @*/
  return rez;
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

