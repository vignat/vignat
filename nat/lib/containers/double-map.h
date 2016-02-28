#ifndef _DOUBLE_MAP_H_INCLUDED_
#define _DOUBLE_MAP_H_INCLUDED_

#include "map.h"

//#define DMAP_CAPACITY (1024)

/*
  This implementation expects keys to be the part of the value:
  value = {
      ...;
key_a_offset: key_a {...};
      ...;
key_b_offset: key_b {...};
      ...;
  };
 */

struct DoubleMap;
/*@
  inductive dmap<t1,t2,vt> = dmap(list<t1>, list<t2>, list<int>, list<vt>, int);

  predicate dmappingp<t1,t2,vt>(dmap<t1,t2,vt> m,
                                predicate (void*,t1) keyp1,
                                predicate (void*,t2) keyp2,
                                predicate (void*,vt) vp,
                                predicate (t1,t2,vt,int) recp,
                                int capacity,
                                struct DoubleMap* mp) = true;

  fixpoint dmap<t1,t2,vt> empty_dmap_fp<t1,t2,vt>();

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
  fixpoint int dmap_size_fp<t1,t2,vt>(dmap<t1,t2,vt> m);
  fixpoint bool dmap_index_used_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);

  fixpoint t1 dmap_get_k1_by_idx_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);
  fixpoint t2 dmap_get_k2_by_idx_fp<t1,t2,vt>(dmap<t1,t2,vt> m, int index);

  lemma void dmap_get_k1_limits<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?vp, ?recp, ?cap, ?mp) &*&
           dmap_has_k1_fp<t1,t2,vt>(m, k1) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, vp, recp, cap, mp) &*&
          0 <= dmap_get_k1_fp<t1,t2,vt>(m, k1) &*&
          dmap_get_k1_fp<t1,t2,vt>(m, k1) < cap;

  lemma void dmap_get_k1_gives_used<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?vp, ?recp, ?cap, ?mp) &*&
           dmap_has_k1_fp<t1,t2,vt>(m, k1) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, vp, recp, cap, mp) &*&
          dmap_index_used_fp(m, dmap_get_k1_fp(m, k1)) == true;

  lemma void dmap_get_k2_gives_used<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?vp, ?recp, ?cap, ?mp) &*&
          dmap_has_k2_fp<t1,t2,vt>(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, vp, recp, cap, mp) &*&
          dmap_index_used_fp(m, dmap_get_k2_fp(m, k2)) == true;

  lemma void dmap_erase_all_has_trans<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1, list<int> idx);
  requires false == dmap_has_k1_fp(m, k1);
  ensures false == dmap_has_k1_fp(dmap_erase_all_fp(m, idx), k1);

  lemma void dmap_get_by_index_rp<t1,t2,vt>(dmap<t1,t2,vt> m, int idx);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?vp, ?recp, ?cap, ?mp) &*&
           dmap_index_used_fp(m, idx) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, vp, recp, cap, mp) &*&
          recp(dmap_get_k1_by_idx_fp(m, idx),
               dmap_get_k2_by_idx_fp(m, idx),
               dmap_get_val_fp(m, idx),
               idx);

  lemma void dmap_get_by_k2_invertible<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2);
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?vp, ?recp, ?cap, ?mp) &*&
           dmap_has_k2_fp(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, vp, recp, cap, mp) &*&
          k2 == dmap_get_k2_by_idx_fp(m, dmap_get_k2_fp(m, k2));

  lemma void dmap_put_get<t1,t2,vt>(dmap<t1,t2,vt> m, vt v,
                                    t1 k1, t2 k2, int index);
  requires dmappingp<t1,t2,vt>(dmap_put_fp(m, k1, k2, index, v),
                              ?kp1, ?kp2, ?vp, ?recp, ?cap, ?mp);
  ensures dmappingp<t1,t2,vt>(dmap_put_fp(m, k1, k2, index, v),
                             kp1, kp2, vp, recp, cap, mp) &*&
          v == dmap_get_val_fp(dmap_put_fp(m, k1, k2, index, v), index) &*&
          k1 == dmap_get_k1_by_idx_fp(dmap_put_fp(m, k1, k2, index, v), index) &*&
          k2 == dmap_get_k2_by_idx_fp(dmap_put_fp(m, k1, k2, index, v), index);
  @*/

/*@ predicate pred_arg4<t1,t2,t3,t4>(predicate (t1,t2,t3,t4) p) = true;
    predicate pred_arg2<t1,t2>(predicate (t1,t2) p) = true;
  @*/

//TODO: rewrite the valp such that it takes the list<char> image of the memory
// and k1, k2. This way I can then easily copy it with memcpy. 
int dmap_allocate/*@ <K1,K2,V> @*/
                 (int key_a_size, int key_a_offset, map_keys_equality* eq_a,
                  int key_b_size, int key_b_offset, map_keys_equality* eq_b,
                  int value_size, int capacity,
                  struct DoubleMap** map_out);
/*@ requires exists<pair<pair<K1,K2>,V > >(pair(pair(_, _), _)) &*&
             [_]is_map_keys_equality<K1>(eq_a, ?keyp1) &*&
             [_]is_map_keys_equality<K2>(eq_b, ?keyp2) &*&
             pred_arg2<void*, V>(?valp) &*&
             pred_arg4<K1,K2,V,int>(?recp) &*&
             pointer(map_out, _) &*&
             0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size; @*/
/*@ ensures result == 0 ? true : (*map_out |-> ?mapp &*&
                                  dmappingp<K1,K2,V>(empty_dmap_fp(), keyp1,
                                                     keyp2, valp, recp,
                                                     capacity, mapp)); @*/

int dmap_get_a/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index);
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?vp, ?rp, ?cap, map) &*&
             kp1(key, ?k1) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, vp, rp, cap, map) &*&
            kp1(key, k1) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 1 &*& *index |-> dmap_get_k1_fp(m, k1)) :
             (result == 0 &*& *index |-> i)); @*/
int dmap_get_b/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index);
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?vp, ?rp, ?cap, map) &*&
             kp2(key, ?k2) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, vp, rp, cap, map) &*&
            kp2(key, k2) &*&
            (dmap_has_k2_fp(m, k2) ?
             (result == 1 &*& *index |-> dmap_get_k2_fp(m, k2)) :
             (result == 0 &*& *index |-> i)); @*/
int dmap_put/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* value, int index);
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?vp, ?rp, ?cap, map) &*&
             vp(value, ?v) &*& rp(?k1, ?k2, v, index) &*&
             false == dmap_index_used_fp(m, index) &*&
             false == dmap_has_k1_fp(m, k1) &*&
             false == dmap_has_k2_fp(m, k2); @*/
/*@ ensures (dmap_size_fp(m) < cap ?
             (result == 1 &*&
              dmappingp<K1,K2,V>(dmap_put_fp(m, k1, k2, index, v),
                                 kp1, kp2, vp, rp, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2,V>(m, kp1, kp2, vp, rp, cap, map))) &*&
            vp(value, v) &*& rp(k1, k2, v, index);@*/
void dmap_get_value/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index, void* value_out);
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?vp, ?rp, ?cap, map); @*/ //Should also require memory access here
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, vp, rp, cap, map) &*&
            dmap_index_used_fp(m, index) ?
            (vp(value_out, dmap_get_val_fp(m, index)) &*&
             rp(dmap_get_k1_by_idx_fp(m, index),
                dmap_get_k2_by_idx_fp(m, index),
                dmap_get_val_fp(m, index),
                index)) :
            true; @*/

int dmap_erase(struct DoubleMap* map, int index);
//^^^ never called, no contract for you.
//^^^ TODO: add the user-defined predicate here somehow.
int dmap_size(struct DoubleMap* map);
//^^^ never called, no contract here.

#endif // _DOUBLE_MAP_H_INCLUDED_
