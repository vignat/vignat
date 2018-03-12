#pragma once


#define RTE_PTYPE_L3_IPV4 0x00000010
#define RTE_ETH_IS_IPV4_HDR(ptype) ((ptype) & RTE_PTYPE_L3_IPV4)
