#include <assert.h>
#include "containers/double-chain.h"
#include "coherence.h"
#include "expirator.h"


/*@
  lemma void expire_0_indexes(dchain ch, uint32_t time)
  requires true;
  ensures ch == expire_n_indexes(ch, time, 0);
  {
    switch(ch) { case dchain(alist, size, l, h):
      take_0(get_expired_indexes_fp(time, alist));
    }
  }
  @*/


/* @
  lemma void erase_nothing<K1,K2,V>(dmap<K1,K2,V> m)
  requires true;
  ensures dmap_erase_all_fp(m, nil) == m;
  {
    switch(m) { case dmap(ks1, ks2, idxs):
    }
  }
  @*/

int expire_items/*@<K1,K2,V> @*/(struct DoubleChain* chain,
                                 struct DoubleMap* map,
                                 uint32_t time)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map) &*&
             double_chainp(?ch, chain) &*&
             dchain_index_range_fp(ch) < INT_MAX &*&
             dmap_dchain_coherent<K1,K2,V>(m, ch); @*/
/*@ ensures dmappingp<K1,K2,V>(?nm,
                               kp1, kp2, hsh1, hsh2, fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map) &*&
            nm == dmap_erase_all_fp
                               (m, dchain_get_expired_indexes_fp(ch, time),
                                vk1, vk2) &*&
            double_chainp(?nch, chain) &*&
            nch == dchain_expire_old_indexes_fp(ch, time) &*&
            dmap_dchain_coherent<K1,K2,V>(nm, nch) &*&
            result == length(dchain_get_expired_indexes_fp(ch, time)); @*/
{
  int count = 0;
  int index = -1;
  //@ expire_0_indexes(ch, time);
  //@ assert take(count, dchain_get_expired_indexes_fp(ch, time)) == nil;
  //@ double_chainp_to_sorted(ch);
  //@ dchain_expired_indexes_limited(ch, time);
  //@ double_chain_nodups(ch);
  while (dchain_expire_one_index(chain, &index, time))
    /*@ invariant double_chainp(expire_n_indexes(ch, time, count), chain) &*&
                  dchain_is_sortedp(ch) &*&
                  dmappingp(dmap_erase_all_fp
                              (m, take(count, dchain_get_expired_indexes_fp
                                               (ch, time)),
                               vk1, vk2),
                            kp1, kp2, hsh1, hsh2, fvp, bvp, rof, vsz,
                            vk1, vk2, rp1, rp2, map) &*&
                  dmap_dchain_coherent(dmap_erase_all_fp
                                        (m, take(count,
                                                 dchain_get_expired_indexes_fp
                                                  (ch, time)),
                                         vk1, vk2),
                                        expire_n_indexes(ch, time, count)) &*&
                  integer(&index, _) &*&
                  dchain_nodups(expire_n_indexes(ch, time, count)) &*&
                  0 <= count &*&
                  count <= length(dchain_get_expired_indexes_fp(ch, time)); @*/
  {
    /*@ dmap<K1,K2,V> cur_m = dmap_erase_all_fp
                               (m, take(count, dchain_get_expired_indexes_fp
                                                (ch, time)),
                                vk1, vk2);
                                @*/
    //@ dchain cur_ch = expire_n_indexes(ch, time, count);
    //@ coherent_old_index_used(cur_m, cur_ch);
    //@ coherent_same_cap(cur_m, cur_ch);
    dmap_erase(map, index);
    //@ expire_n_plus_one(ch, time, count);
    //@ dchain_still_more_to_expire(ch, time, count);
    ++count;
    /*@ dmap_erase_another_one(m, take(count-1, dchain_get_expired_indexes_fp(ch, time)),
                               dchain_get_oldest_index_fp(cur_ch),
                               vk1, vk2);
                               @*/
    //@ dchain_oldest_allocated(cur_ch);
    //@ coherent_expire_one(cur_m, cur_ch, dchain_get_oldest_index_fp(cur_ch), vk1, vk2);
  }
  /*@ if(dchain_is_empty_fp(expire_n_indexes(ch, time, count))) {
      expired_all(ch, time, count);
    } else {
      no_more_expired(ch, time, count);
    }
    @*/
  //@ assert count == length(dchain_get_expired_indexes_fp(ch, time));
  //@ assert take(count, dchain_get_expired_indexes_fp(ch, time)) == dchain_get_expired_indexes_fp(ch, time);
  return count;
  //@ destroy_dchain_is_sortedp(ch);
  //@ destroy_dchain_nodups(expire_n_indexes(ch, time, count));
}

