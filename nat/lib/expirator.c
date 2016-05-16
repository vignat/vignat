#include <assert.h>
#include "containers/double-chain.h"
#include "flowtable.h"
#include "expirator.h"

//@ #include <nat.gh>

/*@
  fixpoint dchain expire_n_indexes(dchain ch, uint32_t time, int n) {
    switch(ch) { case dchain(alist, size):
      return dchain(fold_left(alist, remove_by_index_fp,
                              take(n, get_expired_indexes_fp(time, alist))),
                    size);
    }
  }
  @*/

/*@
  lemma void expire_0_indexes(dchain ch, uint32_t time)
  requires true;
  ensures ch == expire_n_indexes(ch, time, 0);
  {
    switch(ch) { case dchain(alist, size):
      take_0(get_expired_indexes_fp(time, alist));
    }
  }
  @*/

/*@
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
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             double_chainp(?ch, chain); @*/
/*@ ensures dmappingp<K1,K2,V>(dmap_erase_all_fp
                                 (m, dchain_get_expired_indexes_fp(ch, time)),
                               kp1, kp2, hsh1, hsh2, fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            double_chainp(dchain_expire_old_indexes_fp(ch, time), chain) &*&
            result == length(dchain_get_expired_indexes_fp(ch, time)); @*/
{
  int count = 0;
  int index = -1;
  //@ expire_0_indexes(ch, time);
  //@ assert take(count, dchain_get_expired_indexes_fp(ch, time)) == nil;
  //@ erase_nothing(m);
  while (dchain_expire_one_index(chain, &index, time))
    /*@ invariant double_chainp(expire_n_indexes(ch, time, count), chain) &*&
                  dmappingp(dmap_erase_all_fp
                              (m, take(count, dchain_get_expired_indexes_fp
                                               (ch, time))),
                            kp1, kp2, hsh1, hsh2, fvp, bvp, rof, vsz,
                            vk1, vk2, rp1, rp2, cap, map) &*&
                  count < length(dchain_get_expired_indexes_fp(ch, time)); @*/
  {
    dmap_erase(map, index);
    ++count;
  }
  return count;
}

