#ifndef _COHERENCE_H_INCLUDED_
#define _COHERENCE_H_INCLUDED_
#include "containers/vector.h"
#include "containers/map.h"
#include "containers/double-map.h"
#include "containers/double-chain.h"


/*@
  predicate dmap_dchain_coherent<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch);
  @*/

/*@
  predicate map_vec_chain_coherent<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, bool> > v, dchain ch);
  @*/

/*@
  fixpoint bool kkeeper<t>(list<pair<t, void*> > addr_map,
                           pair<t, bool> entry, void* ptr) {
    return snd(entry) ? true :
             (map_has_fp(addr_map, fst(entry)) &&
              ptr == map_get_fp(addr_map, fst(entry)));
  }
  @*/

/*@
  lemma void mvc_coherent_bounds<kt>(list<pair<kt, int> > m,
                                     list<pair<kt, bool> > v, dchain ch);
  requires map_vec_chain_coherent<kt>(m, v, ch);
  ensures dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch);
  @*/
/*@
  lemma void mvc_coherent_index_busy<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, bool> > v, dchain ch,
                                         uint32_t index);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == dchain_allocated_fp(ch, index);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          nth(index, v) == pair(?key, false) &*&
          true == map_has_fp(m, key) &*&
          map_get_fp(m, key) == index;
  @*/
/*@
  lemma void mvc_coherent_map_get_bounded<kt>(list<pair<kt, int> > m,
                                              list<pair<kt, bool> > v, dchain ch,
                                              kt k);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, k);
  ensures 0 <= map_get_fp(m, k) &*& map_get_fp(m, k) < length(v) &*&
          dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == dchain_allocated_fp(ch, map_get_fp(m, k));
  @*/

/*@
  lemma void mvc_coherent_map_get_vec_half<kt>(list<pair<kt, int> > m,
                                               list<pair<kt, bool> > v, dchain ch,
                                               kt k);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == map_has_fp(m, k);
  ensures 0 <= map_get_fp(m, k) &*& map_get_fp(m, k) < length(v) &*&
          dchain_index_range_fp(ch) == length(v) &*&
          map_vec_chain_coherent<kt>(m, v, ch) &*&
          true == dchain_allocated_fp(ch, map_get_fp(m, k)) &*&
          false == snd(nth(map_get_fp(m, k), v));
  @*/

/*@
  lemma void mvc_rejuvenate_preserves_coherent<kt>(list<pair<kt, int> > m,
                                                  list<pair<kt, bool> > v, dchain ch,
                                                  int index, time_t time);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           true == dchain_allocated_fp(ch, index);
  ensures map_vec_chain_coherent<kt>(m, v, dchain_rejuvenate_fp(ch,
                                                                index,
                                                                time));
  @*/

/*@
  lemma void mvc_coherent_alloc_is_halfowned<kt>(list<pair<kt, int> > m,
                                                 list<pair<kt, bool> > v, dchain ch,
                                                 int index);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           0 <= index &*& index < length(v);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          snd(nth(index, v)) != dchain_allocated_fp(ch, index);
  @*/

/*@
  lemma void mvc_coherent_same_len<kt>(list<pair<kt, int> > m,
                                       list<pair<kt, bool> > v, dchain ch);
  requires map_vec_chain_coherent<kt>(m, v, ch);
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          length(v) == dchain_index_range_fp(ch);
  @*/

/*@
  lemma void empty_map_vec_dchain_coherent<kt>(list<pair<kt, bool> > vec);
  requires vec != nil;
  ensures map_vec_chain_coherent<kt>(nil, vec,
                                     empty_dchain_fp(length(vec), 0));
  @*/

/*@
  lemma void mvc_coherent_dchain_non_out_of_space_map_nonfull<kt>(list<pair<kt, int> > m,
                                                                  list<pair<kt, bool> > v, dchain ch);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           dchain_out_of_space_fp(ch) == false;
  ensures map_vec_chain_coherent<kt>(m, v, ch) &*&
          map_size_fp(m) < dchain_index_range_fp(ch);
  @*/

/*@
  lemma void mvc_coherent_put<kt>(list<pair<kt, int> > m,
                                  list<pair<kt, bool> > v, dchain ch,
                                  int index, time_t time,
                                  kt key);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           false == dchain_allocated_fp(ch, index);
  ensures map_vec_chain_coherent<kt>(map_put_fp(m, key, index),
                                     update(index, pair(key, false), v),
                                     dchain_allocate_fp(ch, index, time));
  @*/

/*@
  lemma void mvc_coherent_expire_one<kt>(list<pair<kt, int> > m,
                                         list<pair<kt, bool> > v, dchain ch,
                                         int index,
                                         kt key);
  requires map_vec_chain_coherent<kt>(m, v, ch) &*&
           nth(index, v) == pair(key, false);
  ensures map_vec_chain_coherent<kt>(map_erase_fp(m, key),
                                     vector_erase_fp(v, index),
                                     dchain_remove_index_fp(ch, index));
  @*/

/*@
  lemma void kkeeper_erase_one<t>(list<void*> addrs,
                                  list<pair<t, bool> > contents,
                                  list<pair<t, void*> > addr_map,
                                  int index);
  requires 0 <= index &*& index < length(contents) &*&
           length(contents) <= length(addrs) &*&
           true == forall2(contents, addrs, (kkeeper)(addr_map)) &*&
           nth(index, contents) == pair(?val, false) &*&
           true == no_dups(addrs);
  ensures true == forall2(vector_erase_fp(contents, index), addrs,
                          (kkeeper)(map_erase_fp(addr_map, fst(nth(index, contents)))));
  @*/

/*@
  lemma void empty_kkeeper<t>(list<void*> addrs,
                              list<pair<t, bool> > contents,
                              list<pair<t, void*> > addr_map,
                              int capacity);
  requires length(contents) == capacity &*&
           true == forall(contents, snd);
  ensures true == forall2(contents, addrs, (kkeeper)(addr_map));
  @*/

/*@
lemma void empty_dmap_dchain_coherent<t1,t2,vt>(int len);
requires 0 <= len;
ensures dmap_dchain_coherent<t1,t2,vt>
         (empty_dmap_fp<t1,t2,vt>(len), empty_dchain_fp(len, 0));

lemma void coherent_dmap_used_dchain_allocated<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch, int idx);
requires dmap_dchain_coherent(m, ch) &*& dmap_index_used_fp(m, idx) == true;
ensures dmap_dchain_coherent(m, ch) &*&
        dchain_allocated_fp(ch, idx) == true;

lemma void coherent_same_indexes<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch);
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, ch) &*&
        true == subset(dchain_indexes_fp(ch), dmap_indexes_used_fp(m)) &*&
        true == subset(dmap_indexes_used_fp(m), dchain_indexes_fp(ch));

lemma void rejuvenate_preserves_coherent<t1,t2,vt>
             (dmap<t1,t2,vt> m, dchain ch,
              int index, time_t time);
requires dmap_dchain_coherent(m, ch) &*&
         true == dchain_allocated_fp(ch, index);
ensures dmap_dchain_coherent(m, dchain_rejuvenate_fp(ch, index, time));

lemma void coherent_put_allocated_preserves_coherent<t1,t2,vt>
(dmap<t1,t2,vt> m, dchain ch, t1 k1, t2 k2,
 vt value, int ind, time_t t,
 fixpoint (vt,t1) vk1,
 fixpoint (vt,t2) vk2);
requires dmap_dchain_coherent(m, ch) &*&
         0 <= ind &*& ind < dmap_cap_fp(m);
ensures dmap_dchain_coherent(dmap_put_fp(m, ind, value, vk1, vk2),
                             dchain_allocate_fp(ch, ind, t));

lemma void coherent_dchain_non_out_of_space_map_nonfull<t1,t2,vt>
            (dmap<t1,t2,vt> m, dchain ch);
requires dmappingp<t1,t2,vt>(m, ?a, ?b, ?c, ?d, ?e, ?g, ?h, ?i, ?j, ?k, ?l, ?n, ?f) &*&
         dmap_dchain_coherent(m, ch) &*&
         dchain_out_of_space_fp(ch) == false;
ensures dmappingp<t1,t2,vt>(m, a, b, c, d, e, g, h, i, j, k, l, n, f) &*&
        dmap_dchain_coherent(m, ch) &*&
        dmap_size_fp(m) < dmap_cap_fp(m);

        @*/

/*@
  lemma void coherent_expire_one<t1,t2,vt>(dmap<t1,t2,vt> m,
                                           dchain ch,
                                           int idx,
                                           fixpoint (vt,t1) vk1,
                                           fixpoint (vt,t2) vk2);
  requires dmap_dchain_coherent(m, ch) &*&
           dchain_nodups(ch) &*&
           true == dchain_allocated_fp(ch, idx) &*&
           0 <= idx;
  ensures dmap_dchain_coherent(dmap_erase_fp(m, idx, vk1, vk2),
                               dchain_remove_index_fp(ch, idx)) &*&
          dchain_nodups(dchain_remove_index_fp(ch, idx));
  @*/

/*@
  lemma void coherent_old_index_used<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch);
  requires dmap_dchain_coherent(m, ch) &*&
           false == dchain_is_empty_fp(ch) &*&
           0 <= dchain_get_oldest_index_fp(ch) &*&
           dchain_get_oldest_index_fp(ch) < dchain_index_range_fp(ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          true == dmap_index_used_fp(m, dchain_get_oldest_index_fp(ch));
  @*/

/*@
  lemma void coherent_same_cap<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch);
  requires dmap_dchain_coherent(m, ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          dmap_cap_fp(m) == dchain_index_range_fp(ch);
  @*/

#endif// _COHERENCE_H_INCLUDED_
