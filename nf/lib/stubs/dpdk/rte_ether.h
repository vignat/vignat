#pragma once

#include <inttypes.h>
#include <stdio.h>


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


static inline void
ether_format_addr(char *buf, uint16_t size,
	const struct ether_addr *eth_addr)
{
	snprintf(buf, size, "%02X:%02X:%02X:%02X:%02X:%02X",
		eth_addr->addr_bytes[0],
		eth_addr->addr_bytes[1],
		eth_addr->addr_bytes[2],
		eth_addr->addr_bytes[3],
		eth_addr->addr_bytes[4],
		eth_addr->addr_bytes[5]);
}
