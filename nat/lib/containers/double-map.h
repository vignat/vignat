#ifndef _DOUBLE_MAP_H_INCLUDED_
#define _DOUBLE_MAP_H_INCLUDED_

#include "map.h"

//@ #include "lib/predicates.gh"

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
                             predicate (void*,t1,t2) valp,
                             int capacity,
                             struct DoubleMap* mp) = true;

  fixpoint dmap<t1,t2> empty_dmap_fp();

  fixpoint dmap<t1,t2> dmap_put_fp(dmap<t1,t2> m, t1 k1, t2 k2, int index, void* val);
  fixpoint dmap<t1,t2> dmap_erase_fp(dmap<t1,t2> m, int index);
  fixpoint int dmap_get_k1_fp(dmap<t1,t2> m, t1 k1);
  fixpoint bool dmap_has_k1_fp(dmap<t1,t2> m, t1 k1);
  fixpoint int dmap_get_k2_fp(dmap<t1,t2> m, t2 k2);
  fixpoint bool dmap_has_k2_fp(dmap<t1,t2> m, t2 k2);
  fixpoint void* dmap_get_val_fp(dmap<t1,t2> m, int index);
  fixpoint int dmap_size_fp(dmap<t1,t2> m);
  fixpoint bool dmap_index_used_fp(dmap<t1,t2> m, int index);

  @*/

int dmap_allocate/*@<K1,K2>(predicate (void*,K1,K2) valp)@*/
                 (int key_a_size, int key_a_offset, map_keys_equality* eq_a,
                  int key_b_size, int key_b_offset, map_keys_equality* eq_b,
                  int value_size, int capacity,
                  struct DoubleMap** map_out);
/*@ requires is_map_keys_equality<K1>(eq_a, ?keyp1) &*&
             is_map_keys_equality<K2>(eq_b, ?keyp2) &*&
             0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size; @*/
/*@ ensures result == 0 ? true : (*map_out |-> ?mapp &*&
                                  dmappingp<K1,K2>(empty_dmap_fp(), keyp1,
                                                   keyp2, valp,
                                                   capacity, mapp)); @*/

int dmap_get_a/*@<K1,K2>@*/(struct DoubleMap* map, void* key, int* index);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*&
             kp1(key, k1) &*&
             index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2>(m, kp1, kp2, vp, cap, map) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 0 &*& index |-> dmap_get_k1_fp(m, k1)) :
             (result == 1 &*& index |-> i)); @*/
int dmap_get_b/*@<K1,K2>@*/(struct DoubleMap* map, void* key, int* index);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*&
  kp2(key, k2) &*&
  index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2>(m, kp1, kp2, vp, cap, map) &*&
  (dmap_has_k2_fp(m, k2) ?
  (result == 0 &*& index |-> dmap_get_k2_fp(m, k2)) :
  (result == 1 &*& index |-> i)); @*/
int dmap_put/*@<K1,K2>@*/(struct DoubleMap* map, void* value, int index);
/*@ requires dmapping<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*& vp(value, ?k1, ?k2) &*&
             false == dmap_has_k1_fp(m, k1) &*&
             false == dmap_has_k2_fp(m, k2); @*/
/*@ ensures (dmap_size_fp(m) < cap ?
             (result == 1 &*&
              dmapping<K1,K2>(dmap_put_fp(m, k1, k2, index, value),
                              kp1, kp2, vp, cap, map)) :
             (result == 0 &*&
              dmapping<K2,K2>(m, kp1, kp2, vp, cap, map))) &*&
            vp(value, k1, k2);@*/
void dmap_get_value(struct DoubleMap* map, int index, void* value_out);
/*@ requires dmapping<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, map) &*& @*/
/*@ ensures dmapping<K1,K2>(m, kp1, kp2, vp, cap, map) &*&
            dmap_index_used_fp(m, index) ?
            (result == 1 &*& vp(value_out, ?k1, ?k2) &*&
             dmap_get_k1_fp(m, k1) == index &*&
             dmap_get_k2_fp(m, k2) == index) :
            (result == 0); @*/
            
int dmap_erase(struct DoubleMap* map, int index);
//^^^ never called, no contract for you.
//^^^ TODO: add the user-defined predicate here somehow.
int dmap_size(struct DoubleMap* map);
//^^^ never called, no contract here.

#endif // _DOUBLE_MAP_H_INCLUDED_
