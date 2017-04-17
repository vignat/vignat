#ifndef _DOUBLE_CHAIN_STUB_CONTROL_H_INCLUDED_
#define _DOUBLE_CHAIN_STUB_CONTROL_H_INCLUDED_

#include "lib/containers/double-chain.h"

void dchain_make_space(struct DoubleChain* chain);

void dchain_reset(struct DoubleChain* chain, int index_range);

#endif//_DOUBLE_CHAIN_STUB_CONTROL_H_INCLUDED_
