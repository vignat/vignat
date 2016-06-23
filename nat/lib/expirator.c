#include <assert.h>
#include "containers/double-chain.h"
#include "flowtable.h"
#include "expirator.h"

/*@
  predicate dmap_dchain_coherent<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch) =
    dchain_index_range_fp(ch) == dmap_cap_fp(m) &*&
    true == forall(dchain_indexes_fp(ch), (dmap_index_used_fp)(m));
  @*/

/*@
  lemma void coherent_expire_one<t1,t2,vt>(dmap<t1,t2,vt> m,
                                           dchain ch,
                                           int idx,
                                           fixpoint (vt,t1) vk1,
                                           fixpoint (vt,t2) vk2)
  requires dmap_dchain_coherent(m, ch) &*&
           dchain_nodups(ch) &*&
           true == dchain_allocated_fp(ch, idx);
  ensures dmap_dchain_coherent(dmap_erase_fp(m, idx, vk1, vk2),
                               dchain_remove_index_fp(ch, idx)) &*&
          dchain_nodups(dchain_remove_index_fp(ch, idx));
  {
    open dmap_dchain_coherent(m, ch);
    dmap<t1,t2,vt> nm = dmap_erase_fp(m, idx, vk1, vk2);
    dchain nch = dchain_remove_index_fp(ch, idx);
    dchain_remove_keeps_ir(ch, idx);
    dmap_erase_keeps_cap(m, idx, vk1, vk2);
    assert dchain_index_range_fp(nch) == dmap_cap_fp(nm);
    dchain_remove_idx_from_indexes(ch, idx);
    assert dchain_indexes_fp(nch) ==
           remove(idx, dchain_indexes_fp(ch));
    dchain_nodups_unique_idx(ch, idx);
    dmap_erase_keeps_rest(m, idx, dchain_indexes_fp(ch), vk1, vk2);

    dchain_remove_keeps_nodups(ch, idx);

    close dmap_dchain_coherent(nm, nch);
  }
  @*/

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

/*@
  lemma void coherent_old_index_used<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch) &*&
           false == dchain_is_empty_fp(ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          true == dmap_index_used_fp(m, dchain_get_oldest_index_fp(ch));
  {
    dchain_oldest_allocated(ch);
    open dmap_dchain_coherent(m, ch);
    dchain_indexes_contain_index(ch, dchain_get_oldest_index_fp(ch));
    forall_mem(dchain_get_oldest_index_fp(ch), dchain_indexes_fp(ch),
               (dmap_index_used_fp)(m));
    close dmap_dchain_coherent(m, ch);
  }
  @*/

/*@
  lemma void coherent_same_cap<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          dmap_cap_fp(m) == dchain_index_range_fp(ch);
  {
    open dmap_dchain_coherent(m, ch);
    close dmap_dchain_coherent(m, ch);
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

