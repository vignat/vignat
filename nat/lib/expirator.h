#ifndef _EXPIRATOR_H_INCLUDED_
#define _EXPIRATOR_H_INCLUDED_

#include "containers/double-chain.h"
#include "containers/double-map.h"
#include "coherence.h"

int expire_items/*@<K1,K2,V> @*/(struct DoubleChain* chain,
                                 struct DoubleMap* map,
                                 uint32_t time);
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

#endif //_EXPIRATOR_H_INCLUDED_
