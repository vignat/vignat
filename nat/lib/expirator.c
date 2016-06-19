#include <assert.h>
#include "containers/double-chain.h"
#include "flowtable.h"
#include "expirator.h"

/*@
  predicate dmap_alist_coherent<t1,t2,vt>(dmap<t1,t2,vt> m,
                                          list<pair<int, uint32_t> > alist) =
    switch(alist) {
      case nil: return true;
      case cons(h,t):
        return true == dmap_index_used_fp(m, fst(h)) &*&
               dmap_alist_coherent(m, t);
    };

  predicate dmap_dchain_coherent<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch) =
    switch(ch) { case dchain(alist, size, l, h):
      return size == dmap_cap_fp(m) &*&
      dmap_alist_coherent(m, alist);
    };
  @*/

/*@
  lemma void coherent_expire_one<t1,t2,vt>(dmap<t1,t2,vt> m,
                                           dchain ch,
                                           int idx,
                                           fixpoint (vt,t1) vk1,
                                           fixpoint (vt,t2) vk2)
  requires dmap_dchain_coherent(m, ch) &*&
           true == dchain_allocated_fp(ch, idx);
  ensures dmap_dchain_coherent(dmap_erase_fp(m, idx, vk1, vk2),
                               dchain_remove_index_fp(ch, idx));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void dchain_oldest_allocated(dchain ch)
  requires false == dchain_is_empty_fp(ch);
  ensures true == dchain_allocated_fp(ch, dchain_get_oldest_index_fp(ch));
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
      assume(false);//TODO
    }
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
  lemma void expired_all(dchain ch, uint32_t time, int count)
  requires true == dchain_is_empty_fp(expire_n_indexes(ch, time, count));
  ensures count == length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_expire_old_indexes_fp(ch, time) ==
          expire_n_indexes(ch, time, count);
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void no_more_expired(dchain ch, uint32_t time, int count)
  requires time <=
           dchain_get_oldest_time_fp(expire_n_indexes(ch, time, count));
  ensures count == length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_expire_old_indexes_fp(ch, time) ==
          expire_n_indexes(ch, time, count);
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void coherent_old_index_used<t1,t2,vt>(dmap<t1,t2,vt> m, dchain ch)
  requires dmap_dchain_coherent(m, ch) &*&
           false == dchain_is_empty_fp(ch);
  ensures dmap_dchain_coherent(m, ch) &*&
          true == dmap_index_used_fp(m, dchain_get_oldest_index_fp(ch));
  {
    assume(false);//TODO
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
    ++count;
    /*@ dmap_erase_another_one(m, take(count-1, dchain_get_expired_indexes_fp(ch, time)),
                               dchain_get_oldest_index_fp(cur_ch),
                               vk1, vk2);
                               @*/
    //@ dchain_oldest_allocated(cur_ch);
    //@ coherent_expire_one(cur_m, cur_ch, dchain_get_oldest_index_fp(cur_ch), vk1, vk2);
    //@ assume(count <= length(dchain_get_expired_indexes_fp(ch, time)));//TODO
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
}

