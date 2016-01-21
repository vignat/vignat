#ifndef _EXPIRATOR_H_INCLUDED_
#define _EXPIRATOR_H_INCLUDED_

#include "flow.h"

void init_expirator(uint32_t expiration_time/*seconds*/);
int expire_flows(uint32_t time);

#endif //_EXPIRATOR_H_INCLUDED_
