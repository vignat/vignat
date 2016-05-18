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
  predicate valsp<vt>(void* values, int val_size, predicate (void*,vt) vp,
                      int length, list<option<vt> > vals) =
     switch(vals) {
       case nil: return length == 0;
       case cons(h,t):
         return switch(h) {
           case none: return chars(values, val_size, _) &*&
                             valsp(values + val_size,
                                   val_size, vp, length-1, t);
           case some(v): return vp(values, v) &*&
                             valsp(values + val_size,
                                   val_size, vp, length-1, t);
         };
     };

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
                                fixpoint (t1,int,bool) recp1,
                                fixpoint (t2,int,bool) recp2,
                                int capacity,
                                struct DoubleMap* mp) =
    malloc_block_DoubleMap(mp) &*&
    mp->value_size |-> val_size &*&
    0 <= val_size &*& val_size < capacity &*&
    mp->cpy |-> ?v_cpy &*&
    [_]is_uq_value_copy<vt>(v_cpy, full_vp, val_size) &*&
    mp->values |-> ?values &*&
    valsp(values, val_size, full_vp, capacity, ?val_arr) &*&
    malloc_block(values, val_size*capacity) &*&
    mp->bbs_a |-> ?bbs_a &*& malloc_block_ints(bbs_a, capacity) &*&
    mp->kps_a |-> ?kps_a &*& malloc_block_pointers(kps_a, capacity) &*&
    mp->khs_a |-> ?khs_a &*& malloc_block_ints(khs_a, capacity) &*&
    mp->inds_a |-> ?inds_a &*& malloc_block_ints(inds_a, capacity) &*&
    mapping(?ma, keyp1, recp1, hsh1, capacity,
            bbs_a, kps_a, khs_a, inds_a) &*&
    mp->eq_a |-> ?eq_a &*&
    [_]is_map_keys_equality<t1>(eq_a, keyp1) &*&
    mp->hsh_a |-> ?hsh_a &*&
    [_]is_map_key_hash<t1>(hsh_a, keyp1, hsh1) &*&
    mp->bbs_b |-> ?bbs_b &*& malloc_block_ints(bbs_b, capacity) &*&
    mp->kps_b |-> ?kps_b &*& malloc_block_pointers(kps_b, capacity) &*&
    mp->khs_b |-> ?khs_b &*& malloc_block_ints(khs_b, capacity) &*&
    mp->inds_b |-> ?inds_b &*& malloc_block_ints(inds_b, capacity) &*&
    mapping(?mb, keyp2, recp2, hsh2, capacity,
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
                         right_offsets, vk1, vk2) &*&
    mp->capacity |-> capacity &*&
    mp->n_vals |-> dmap_size_fp(m) &*&
    0 <= capacity &*& capacity < 4096 &*&
    m == dmap(ma, mb, val_arr);
  @*/

/*@
  lemma void empty_valsp<vt>(void* values, int val_size,
                             predicate (void*,vt) vp, nat len)
  requires chars(values, val_size*int_of_nat(len), _) &*&
           0 <= val_size;
  ensures valsp(values, val_size, vp, int_of_nat(len),
                empty_vals_fp(len));
  {
    switch(len) {
      case zero:
        close valsp(values, val_size, vp, 0, nil);
        return;
      case succ(n):
        assume(val_size < val_size*int_of_nat(len)); //TODO
        assume(val_size*int_of_nat(len) - val_size == val_size*int_of_nat(n));
        chars_split(values, val_size);
        empty_valsp(values + val_size, val_size, vp, n);
        close valsp(values, val_size, vp, int_of_nat(len),
                    empty_vals_fp(len));
        return;
    }
  }
  @*/
int dmap_allocate/*@ <K1,K2,V> @*/
                 (map_keys_equality* eq_a, map_key_hash* hsh_a,
                  map_keys_equality* eq_b, map_key_hash* hsh_b,
                  int value_size, uq_value_copy* v_cpy,
                  dmap_extract_keys* dexk,
                  dmap_pack_keys* dpk,
                  int capacity,
                  struct DoubleMap** map_out)
/*@ requires dmap_key_val_types<K1,K2,V>(_, _, _) &*&
             [_]is_map_keys_equality<K1>(eq_a, ?keyp1) &*&
             [_]is_map_key_hash<K1>(hsh_a, keyp1, ?hsh1) &*&
             [_]is_map_keys_equality<K2>(eq_b, ?keyp2) &*&
             [_]is_map_key_hash<K2>(hsh_b, keyp2, ?hsh2) &*&
             [_]is_uq_value_copy<V>(v_cpy, ?fvp, value_size) &*&
             [_]is_dmap_extract_keys(dexk, keyp1, keyp2, fvp,
                                     ?bvp, ?rof, ?vk1, ?vk2) &*&
             [_]is_dmap_pack_keys(dpk, keyp1, keyp2, fvp, bvp, rof, vk1, vk2) &*&
             dmap_record_property1<K1>(?recp1) &*&
             dmap_record_property2<K2>(?recp2) &*&
             *map_out |-> ?old_map_out &*&
             0 < value_size &*& value_size < capacity &*&
             capacity < 4096; @*/
/*@ ensures result == 0 ?
            (*map_out |-> old_map_out) :
            (*map_out |-> ?mapp &*&
             result == 1 &*&
             dmappingp<K1,K2,V>(empty_dmap_fp(capacity), keyp1,
                                keyp2, hsh1, hsh2, fvp, bvp, rof, value_size,
                                vk1, vk2, recp1, recp2,
                                capacity, mapp)); @*/
{
  //@ open dmap_key_val_types(?def_k1, ?def_k2, ?def_val);
  //@ open dmap_record_property1(_);
  //@ open dmap_record_property2(_);
  struct DoubleMap* old_map_val = *map_out;
  struct DoubleMap* map_alloc = malloc(sizeof(struct DoubleMap));
  if (map_alloc == NULL) return 0;
  *map_out = (struct DoubleMap*) map_alloc;

  //@ mul_bounds(value_size, 4096, capacity, 4096);
  uint8_t* vals_alloc = malloc(value_size*capacity);
  if (vals_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->values = vals_alloc;
  int* bbs_a_alloc = malloc(sizeof(int)*capacity);
  if (bbs_a_alloc == NULL) {
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_a = bbs_a_alloc;
  void** kps_a_alloc = malloc(sizeof(void*)*capacity);
  if (kps_a_alloc == NULL) {
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_a = kps_a_alloc;
  int* khs_a_alloc = malloc(sizeof(int)*capacity);
  if (khs_a_alloc == NULL) {
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_a = khs_a_alloc;
  int* inds_a_alloc = malloc(sizeof(int)*capacity);
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
  int* bbs_b_alloc = malloc(sizeof(int)*capacity);
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
  void** kps_b_alloc = malloc(sizeof(void*)*capacity);
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
  int* khs_b_alloc = malloc(sizeof(int)*capacity);
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
  int* inds_b_alloc = malloc(sizeof(int)*capacity);
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

  //@ close map_key_type(def_k1);
  //@ close map_key_hash(hsh1);
  //@ close map_record_property(recp1);
  map_initialize((*map_out)->bbs_a, (*map_out)->eq_a,
                 (*map_out)->kps_a, (*map_out)->khs_a, (*map_out)->inds_a,
                 (*map_out)->capacity);
  //@ close map_key_type(def_k2);
  //@ close map_key_hash(hsh2);
  //@ close map_record_property(recp2);
  map_initialize((*map_out)->bbs_b, (*map_out)->eq_b,
                 (*map_out)->kps_b, (*map_out)->khs_b, (*map_out)->inds_b,
                 (*map_out)->capacity);

  (*map_out)->n_vals = 0;
  //@ empty_valsp(vals_alloc, value_size, fvp, nat_of_int(capacity));
  /*@ close dmappingp<K1,K2,V>(empty_dmap_fp<K1,K2,V>(capacity), keyp1, keyp2,
                               hsh1, hsh2,
                               fvp, bvp, rof, value_size,
                               vk1, vk2, recp1, recp2, capacity, *map_out);
    @*/
  return 1;
}

/*@
  predicate hide_map_key_hash<kt>(map_key_hash* hsh, predicate (void*;kt) keyp,
                                  fixpoint (kt,int) hshfp) =
    is_map_key_hash<kt>(hsh, keyp, hshfp);

  predicate hide_mapping<kt>(list<pair<kt,int> > m,
                             predicate (void*;kt) keyp,
                             fixpoint (kt,int,bool) recp,
                             fixpoint (kt,int) hash,
                             int capacity,
                             int* busybits,
                             void** keyps,
                             int* k_hashes,
                             int* values) =
    mapping<kt>(m, keyp, recp, hash, capacity, busybits, keyps, k_hashes, values);
  @*/

int dmap_get_a/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             kp1(key, ?k1) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            kp1(key, k1) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k1_fp(m, k1) &*&
              true == rp1(k1, ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  map_key_hash *hsh_a = map->hsh_a;
  //@ map_key_hash *hsh_b = map->hsh_b;
  //@ assert [?x]is_map_key_hash(hsh_b, kp2, hsh2);
  //@ close [x]hide_map_key_hash(map->hsh_b, kp2, hsh2);
  int hash = hsh_a(key);
  //@ open [x]hide_map_key_hash(map->hsh_b, kp2, hsh2);
  int rez = map_get(map->bbs_a, map->kps_a, map->khs_a, map->inds_a, key,
                    map->eq_a, hash, index,
                    map->capacity);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  return rez;
}

int dmap_get_b/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             kp2(key, ?k2) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            kp2(key, k2) &*&
            (dmap_has_k2_fp(m, k2) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k2_fp(m, k2) &*&
              true == rp2(k2, ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  map_key_hash *hsh_b = map->hsh_b;
  //@ map_key_hash *hsh_a = map->hsh_a;
  //@ assert [?x]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  int hash = hsh_b(key);
  //@ open [x]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ int* bbs1 = map->bbs_a;
  //@ void** kps1 = map->kps_a;
  //@ int* khs1 = map->khs_a;
  //@ int* vals1 = map->inds_a;
  //@ assert mapping(?m1, kp1, rp1, hsh1, cap, bbs1, kps1, khs1, vals1);
  //@ close hide_mapping(m1, kp1, rp1, hsh1, cap, bbs1, kps1, khs1, vals1);
  return map_get(map->bbs_b, map->kps_b, map->khs_b, map->inds_b, key,
                 map->eq_b, hash, index,
                 map->capacity);
  //@ open hide_mapping(_, _, _, _, _, _, _, _, _);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
}

int dmap_put/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* value, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             fvp(value, ?v) &*&
             true == rp1(vk1(v), index) &*&
             true == rp2(vk2(v), index) &*&
             false == dmap_index_used_fp(m, index) &*&
             false == dmap_has_k1_fp(m, vk1(v)) &*&
             false == dmap_has_k2_fp(m, vk2(v)) &*&
             0 <= index &*& index < cap; @*/
/*@ ensures (dmap_size_fp(m) < cap ?
             (result == 1 &*&
              dmappingp<K1,K2,V>(dmap_put_fp(m, index, v, vk1, vk2),
                                 kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map))) &*&
            fvp(value, v);@*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  void* key_a = 0;
  void* key_b = 0;
  //@ mul_bounds(index, 4096, vsz, 4096);
  void* my_value = map->values + index*map->value_size;
  map->cpy(my_value, value);
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
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  return ret;
}

void dmap_get_value/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index,
                                     void* value_out)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             fvp(value_out, _) &*&
             0 <= index &*& index < cap; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            fvp(value_out, dmap_get_val_fp(m, index)); @*/
{
  map->cpy(value_out, map->values + index*map->value_size);
}

int dmap_erase/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             0 <= index &*& index < cap; @*/
/*@ ensures (dmap_index_used_fp(m, index) ?
             (result == 1 &*&
              dmappingp<K1,K2,V>(dmap_erase_fp(m, index, vk1, vk2),
                                 kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map) &*&
              fvp(_, dmap_get_val_fp(m, index))) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map))); @*/
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
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map); @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            result == dmap_size_fp(m); @*/
{
  return map->n_vals;
}

