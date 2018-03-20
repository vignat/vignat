// used with VeriFast, no pragma
#ifndef RTE_ETHER_H
#define RTE_ETHER_H

#include <stdint.h>
#include <stdio.h>


#define ETHER_TYPE_IPv4 0x0800
#define ETHER_MAX_LEN 1518


struct ether_addr {
// Inline the array for convenience in proofs
//	uint8_t addr_bytes[6];
	uint8_t a;
	uint8_t b;
	uint8_t c;
	uint8_t d;
	uint8_t e;
	uint8_t f;
};

struct ether_hdr {
	struct ether_addr d_addr;
	struct ether_addr s_addr;
	uint16_t ether_type;
};


static void
ether_format_addr(char *buf, uint16_t size, const struct ether_addr *eth_addr)
{
	snprintf(buf, size, "%02X:%02X:%02X:%02X:%02X:%02X",
		eth_addr->a,
		eth_addr->b,
		eth_addr->c,
		eth_addr->d,
		eth_addr->e,
		eth_addr->f);
}

#endif
