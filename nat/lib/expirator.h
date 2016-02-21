#ifndef _EXPIRATOR_H_INCLUDED_
#define _EXPIRATOR_H_INCLUDED_

#include "containers/double-chain.h"
#include "containers/double-map.h"

int expire_items(struct DoubleChain* chain, struct DoubleMap* map,
                 uint32_t time);

#endif //_EXPIRATOR_H_INCLUDED_
