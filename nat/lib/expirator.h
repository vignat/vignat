#ifndef _EXPIRATOR_H_INCLUDED_
#define _EXPIRATOR_H_INCLUDED_

#include "containers/double-chain.h"
#include "containers/double-map.h"

int expire_items/*@<K1,K2,V> @*/(struct DoubleChain* chain,
                                 struct DoubleMap* map,
                                 uint32_t time);
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
//^^^ TODO: also ensures that all the items left are newer than "time";

#endif //_EXPIRATOR_H_INCLUDED_
