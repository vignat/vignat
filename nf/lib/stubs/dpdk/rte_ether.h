#pragma once

#include <inttypes.h>


#define ETHER_TYPE_IPv4 0x0800
#define ETHER_MAX_LEN 1518


struct ether_addr {
	uint8_t addr_bytes[6];
};

struct ether_hdr {
	struct ether_addr d_addr;
	struct ether_addr s_addr;
	uint16_t ether_type;
};
