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
  inductive dmap<t1,t2> = dmap(list<t1>, list<t2>, int);

  predicate dmappingp<t1,t2>(dmap<t1,t2> m,
                             predicate (void*,t1) keyp1,
                             predicate (void*,t2) keyp2,
                             predicate (void*,t1,t2,int) valp,
                             int capacity,
                             struct DoubleMap* mp) = true;

  fixpoint dmap<t1,t2> empty_dmap_fp<t1,t2>();

  fixpoint dmap<t1,t2> dmap_put_fp<t1,t2>(dmap<t1,t2> m, t1 k1, t2 k2, int index, void* val);
  fixpoint dmap<t1,t2> dmap_erase_fp<t1,t2>(dmap<t1,t2> m, int index);
  fixpoint dmap<t1,t2> dmap_erase_all_fp<t1,t2>(dmap<t1,t2> m, list<int> indexes);
  fixpoint int dmap_get_k1_fp<t1,t2>(dmap<t1,t2> m, t1 k1);
  fixpoint bool dmap_has_k1_fp<t1,t2>(dmap<t1,t2> m, t1 k1);
  fixpoint int dmap_get_k2_fp<t1,t2>(dmap<t1,t2> m, t2 k2);
  fixpoint bool dmap_has_k2_fp<t1,t2>(dmap<t1,t2> m, t2 k2);
  fixpoint void* dmap_get_val_fp<t1,t2>(dmap<t1,t2> m, int index);
  fixpoint int dmap_size_fp<t1,t2>(dmap<t1,t2> m);
  fixpoint bool dmap_index_used_fp<t1,t2>(dmap<t1,t2> m, int index);

  lemma void dmap_get_k1_limits<t1,t2>(dmap<t1,t2> m, t1 k1);
  requires dmappingp<t1,t2>(m, ?kp1, ?kp2, ?vp, ?cap, ?mp) &*&
           dmap_has_k1_fp<t1,t2>(m, k1) == true;
  ensures dmappingp<t1,t2>(m, kp1, kp2, vp, cap, mp) &*&
          0 <= dmap_get_k1_fp<t1,t2>(m, k1) &*&
          dmap_get_k1_fp<t1,t2>(m, k1) < cap;

  lemma void dmap_get_k1_gives_used<t1,t2>(dmap<t1,t2> m, t1 k1);
  requires dmappingp<t1,t2>(m, ?kp1, ?kp2, ?vp, ?cap, ?mp) &*&
           dmap_has_k1_fp<t1,t2>(m, k1) == true;
  ensures dmappingp<t1,t2>(m, kp1, kp2, vp, cap, mp) &*&
          dmap_index_used_fp(m, dmap_get_k1_fp(m, k1)) == true;

  lemma void dmap_erase_all_has_trans<t1,t2>(dmap<t1,t2> m, t1 k1, list<int> idx);
  requires false == dmap_has_k1_fp(m, k1);
  ensures false == dmap_has_k1_fp(dmap_erase_all_fp(m, idx), k1);
  @*/

/*@ predicate pred_arg4<t1,t2,t3,t4>(predicate (t1,t2,t3,t4) p) = true;
  @*/

//TODO: rewrite the valp such that it takes the list<char> image of the memory
// and k1, k2. This way I can then easily copy it with memcpy. 
int dmap_allocate/*@ <K1,K2> @*/
                 (int key_a_size, int key_a_offset, map_keys_equality* eq_a,
                  int key_b_size, int key_b_offset, map_keys_equality* eq_b,
                  int value_size, int capacity,
                  struct DoubleMap** map_out);
/*@ requires exists<pair<K1,K2> >(pair(?gg1, ?gg2)) &*&
             [_]is_map_keys_equality<K1>(eq_a, ?keyp1) &*&
             [_]is_map_keys_equality<K2>(eq_b, ?keyp2) &*&
             pred_arg4<void*,K1,K2,int>(?valp) &*&
             pointer(map_out, _) &*&
             0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size; @*/
/*@ ensures result == 0 ? true : (*map_out |-> ?mapp &*&
                                  dmappingp<K1,K2>(empty_dmap_fp(), keyp1,
                                                   keyp2, valp,
                                                   capacity, mapp)); @*/

int dmap_get_a/*@ <K1,K2> @*/(struct DoubleMap* map, void* key, int* index);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*&
             kp1(key, ?k1) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2>(m, kp1, kp2, vp, cap, map) &*&
            kp1(key, k1) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 1 &*& *index |-> dmap_get_k1_fp(m, k1)) :
             (result == 0 &*& *index |-> i)); @*/
int dmap_get_b/*@ <K1,K2> @*/(struct DoubleMap* map, void* key, int* index);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*&
             kp2(key, ?k2) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2>(m, kp1, kp2, vp, cap, map) &*&
            kp2(key, k2) &*&
            (dmap_has_k2_fp(m, k2) ?
             (result == 1 &*& *index |-> dmap_get_k2_fp(m, k2)) :
             (result == 0 &*& *index |-> i)); @*/
int dmap_put/*@ <K1,K2> @*/(struct DoubleMap* map, void* value, int index);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*&
             vp(value, ?k1, ?k2, index) &*&
             false == dmap_has_k1_fp(m, k1) &*&
             false == dmap_has_k2_fp(m, k2); @*/
/*@ ensures (dmap_size_fp(m) < cap ?
             (result == 1 &*&
              dmappingp<K1,K2>(dmap_put_fp(m, k1, k2, index, value),
                               kp1, kp2, vp, cap, map)) :
             (result == 0 &*&
              dmappingp<K1,K2>(m, kp1, kp2, vp, cap, map))) &*&
            vp(value, k1, k2, index);@*/
void dmap_get_value/*@ <K1,K2> @*/(struct DoubleMap* map, int index, void* value_out);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map); @*/ //Should also require memory access here
/*@ ensures dmappingp<K1,K2>(m, kp1, kp2, vp, cap, map) &*&
            dmap_index_used_fp(m, index) ?
            (vp(value_out, ?k1, ?k2, index) &*&
             dmap_get_k1_fp(m, k1) == index &*&
             dmap_get_k2_fp(m, k2) == index) :
            true; @*/

int dmap_erase(struct DoubleMap* map, int index);
//^^^ never called, no contract for you.
//^^^ TODO: add the user-defined predicate here somehow.
int dmap_size(struct DoubleMap* map);
//^^^ never called, no contract here.

#endif // _DOUBLE_MAP_H_INCLUDED_
