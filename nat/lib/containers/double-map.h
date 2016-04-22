#ifndef _DOUBLE_MAP_H_INCLUDED_
#define _DOUBLE_MAP_H_INCLUDED_

#include "map.h"

/*
  This implementation expects keys to be the part of the value. The keys
  are extracted with dmap_extract_keys function and are put back with
  dmap_pack_keys.
 */

typedef int map_key_hash/*@ <K>(predicate (void*; K) keyp,
                                fixpoint (K,int) hash) @*/(void* k1);
//@ requires keyp(k1, ?kk1);
//@ ensures keyp(k1, kk1) &*& result == hash(kk1);

typedef void uq_value_copy/*@<K>(predicate (void*, K) vp, int size) @*/(char* dst, void* src);
//@ requires vp(src, ?v) &*& dst[0..size] |-> _;
//@ ensures vp(src, v) &*& vp(dst, v);

typedef void dmap_extract_keys/*@ <K1,K2,V>
                                (predicate (void*; K1) keyp1,
                                 predicate (void*; K2) keyp2,
                                 predicate (void*, V) full_valp,
                                 predicate (void*, V) bare_valp,
                                 fixpoint (void*, void*, void*, bool)
                                   right_offsets,
                                 fixpoint (V,K1) vk1,
                                 fixpoint (V,K2) vk2)
                              @*/
                              (void* vp, void** kpp1, void** kpp2);
//@ requires full_valp(vp, ?v) &*& *kpp1 |-> _ &*& *kpp2 |-> _;
/*@ ensures bare_valp(vp, v) &*& *kpp1 |-> ?kp1 &*& *kpp2 |-> ?kp2 &*&
            keyp1(kp1, ?k1) &*& keyp2(kp2, ?k2) &*&
            true == right_offsets(vp, kp1, kp2) &*&
            k1 == vk1(v) &*&
            k2 == vk2(v); @*/

typedef void dmap_pack_keys/*@ <K1,K2,V>
                             (predicate (void*; K1) keyp1,
                              predicate (void*; K2) keyp2,
                              predicate (void*, V) full_valp,
                              predicate (void*, V) bare_valp,
                              fixpoint (void*, void*, void*, bool)
                                right_offsets,
                              fixpoint (V,K1) vk1,
                              fixpoint (V,K2) vk2)
                           @*/
                           (void* vp, void* kp1, void* kp2);
/*@ requires bare_valp(vp, ?v) &*& keyp1(kp1, ?k1) &*& keyp2(kp2, ?k2) &*&
             true == right_offsets(vp, kp1, kp2) &*&
             k1 == vk1(v) &*&
             k2 == vk2(v); @*/
//@ ensures full_valp(vp, v);

struct DoubleMap;
/*@
  inductive dmap<t1,t2,vt> = dmap(list<pair<t1,int> >, list<pair<t2,int> >, list<pair<int,vt> >);

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
                                struct DoubleMap* mp);

  fixpoint dmap<t1,t2,vt> empty_dmap_fp<t1,t2,vt>() {
    return dmap(nil, nil, nil);
  }

  fixpoint dmap<t1,t2,vt> dmap_put_fp<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                t1 k1, t2 k2, int index,
                                                vt v);
  fixpoint dmap<t1,t2,vt> dmap_erase_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);
  fixpoint dmap<t1,t2,vt> dmap_erase_all_fp<t1,t2,vt>(dmap<t1,t2,vt> m, list<int> indexes);
  fixpoint int dmap_get_k1_fp<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1);
  fixpoint bool dmap_has_k1_fp<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1);
  fixpoint int dmap_get_k2_fp<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  fixpoint bool dmap_has_k2_fp<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  fixpoint vt dmap_get_val_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);
  fixpoint int dmap_size_fp<t1,t2,vt>(dmap<t1,t2,vt> m) {
    switch(m) { case dmap(m1, m2, vals): return length(vals); }
  }
  fixpoint bool dmap_index_used_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);

  fixpoint t1 dmap_get_k1_by_idx_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);
  fixpoint t2 dmap_get_k2_by_idx_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);

  lemma void dmap_get_k1_limits<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           dmap_has_k1_fp<t1,t2,vt>(m, k1) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2, fvp,
                              bvp, rof, vsz, vk1, vk2, recp1, recp2, cap, mp) &*&
          0 <= dmap_get_k1_fp<t1,t2,vt>(m, k1) &*&
          dmap_get_k1_fp<t1,t2,vt>(m, k1) < cap;

  lemma void dmap_get_k2_limits<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           dmap_has_k2_fp<t1,t2,vt>(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          0 <= dmap_get_k2_fp<t1,t2,vt>(m, k2) &*&
          dmap_get_k2_fp<t1,t2,vt>(m, k2) < cap;

  lemma void dmap_get_k1_gives_used<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           dmap_has_k1_fp<t1,t2,vt>(m, k1) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          dmap_index_used_fp(m, dmap_get_k1_fp(m, k1)) == true;

  lemma void dmap_get_k2_gives_used<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
          dmap_has_k2_fp<t1,t2,vt>(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          dmap_index_used_fp(m, dmap_get_k2_fp(m, k2)) == true;

  lemma void dmap_erase_all_has_trans<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1, list<int> idx);
  requires false == dmap_has_k1_fp(m, k1);
  ensures false == dmap_has_k1_fp(dmap_erase_all_fp(m, idx), k1);

  lemma void dmap_get_by_index_rp<t1,t2,vt>(dmap<t1,t2,vt> m, int idx);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           dmap_index_used_fp(m, idx) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          true == recp1(dmap_get_k1_by_idx_fp(m, idx),
                        idx) &*&
          true == recp2(dmap_get_k2_by_idx_fp(m, idx),
                        idx);

  lemma void dmap_get_by_k2_invertible<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           dmap_has_k2_fp(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          k2 == dmap_get_k2_by_idx_fp(m, dmap_get_k2_fp(m, k2));

  lemma void dmap_put_get<t1,t2,vt>(dmap<t1,t2,vt> m, vt v,
                                    t1 k1, t2 k2, int index);
  requires dmappingp<t1,t2,vt>(dmap_put_fp(m, k1, k2, index, v),
                               ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp);
  ensures dmappingp<t1,t2,vt>(dmap_put_fp(m, k1, k2, index, v),
                              kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          dmap_index_used_fp(dmap_put_fp(m, k1, k2, index, v), index) == true &*&
          v == dmap_get_val_fp(dmap_put_fp(m, k1, k2, index, v), index) &*&
          k1 == dmap_get_k1_by_idx_fp(dmap_put_fp(m, k1, k2, index, v), index) &*&
          k2 == dmap_get_k2_by_idx_fp(dmap_put_fp(m, k1, k2, index, v), index);

  lemma void dmap_get_k1_get_val<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k);
  requires dmappingp<t1,t2,vt>(m,
                               ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           true == dmap_has_k1_fp(m, k);
  ensures dmappingp<t1,t2,vt>(m,
                              kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          vk1(dmap_get_val_fp(m, dmap_get_k1_fp(m, k))) == k &*&
          true == recp2(vk2(dmap_get_val_fp(m, dmap_get_k1_fp(m, k))), dmap_get_k1_fp(m,k)) &*&
          true == recp1(k, dmap_get_k1_fp(m,k));

  lemma void dmap_get_k2_get_val<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k);
  requires dmappingp<t1,t2,vt>(m,
                               ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?cap, ?mp) &*&
           true == dmap_has_k2_fp(m, k);
  ensures dmappingp<t1,t2,vt>(m,
                              kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, cap, mp) &*&
          vk2(dmap_get_val_fp(m, dmap_get_k2_fp(m, k))) == k &*&
          true == recp1(vk1(dmap_get_val_fp(m, dmap_get_k2_fp(m, k))), dmap_get_k2_fp(m,k)) &*&
          true == recp2(k, dmap_get_k2_fp(m,k));
  @*/

/*@ predicate dmap_key_val_types<K1,K2,V>(K1 k1, K2 k2, V v) = true;
    predicate dmap_record_property1<K1>(fixpoint(K1,int,bool) prop) = true;
    predicate dmap_record_property2<K2>(fixpoint(K2,int,bool) prop) = true;
  @*/

int dmap_allocate/*@ <K1,K2,V> @*/
                 (map_keys_equality* eq_a, map_key_hash* hsh_a,
                  map_keys_equality* eq_b, map_key_hash* hsh_b,
                  int value_size, uq_value_copy* v_cpy,
                  dmap_extract_keys* dexk,
                  dmap_pack_keys* dpk,
                  int capacity,
                  struct DoubleMap** map_out);
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
             dmappingp<K1,K2,V>(empty_dmap_fp(), keyp1,
                                keyp2, hsh1, hsh2, fvp, bvp, rof, value_size,
                                vk1, vk2, recp1, recp2,
                                capacity, mapp)); @*/

int dmap_get_a/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index);
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

int dmap_get_b/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index);
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

int dmap_put/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* value, int index);
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
              dmappingp<K1,K2,V>(dmap_put_fp(m, vk1(v), vk2(v), index, v),
                                 kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map))) &*&
            fvp(value, v);@*/

void dmap_get_value/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index,
                                     void* value_out);
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

int dmap_erase/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index);
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             0 <= index &*& index < cap; @*/
/*@ ensures (dmap_index_used_fp(m, index) ?
             (result == 1 &*&
              dmappingp<K1,K2,V>(dmap_erase_fp(m, index),
                                 kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                                 fvp, bvp, rof, vsz,
                                 vk1, vk2, rp1, rp2, cap, map))) &*&
              fvp(_, dmap_get_val_fp(m, index)); @*/

int dmap_size/*@ <K1,K2,V> @*/(struct DoubleMap* map);
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map); @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            result == dmap_size_fp(m); @*/

#endif // _DOUBLE_MAP_H_INCLUDED_
