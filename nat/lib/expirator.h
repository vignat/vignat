#ifndef _EXPIRATOR_H_INCLUDED_
#define _EXPIRATOR_H_INCLUDED_

#include "containers/double-chain.h"
#include "containers/double-map.h"

int expire_items/*@<K1,K2> @*/(struct DoubleChain* chain,
                              struct DoubleMap* map,
                              uint32_t time);
/*@ requires dmappingp<K1,K2>(?m, ?kp1, ?kp2, ?vp, ?cap, ?mp) &*&
             double_chainp(?ch, ?ir, ?chp); @*/
/*@ ensures dmappingp<K1,K2>(m, kp1, kp2, vp, cap, mp) &*&
            double_chainp(ch, ir, chp) &*& result >= 0; @*/
//^^^ TODO: also ensures that all the items left are newer than "time";

#endif //_EXPIRATOR_H_INCLUDED_
