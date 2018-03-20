// used with VeriFast, no pragma
#ifndef RTE_IP_H
#define RTE_IP_H

#include <stdint.h>


#define IPV4_HDR_IHL_MASK 0x0F
#define IPV4_IHL_MULTIPLIER 4


struct ipv4_hdr {
	uint8_t version_ihl;
	uint8_t type_of_service;
	uint16_t total_length;
	uint16_t packet_id;
	uint16_t fragment_offset;
	uint8_t time_to_live;
	uint8_t next_proto_id;
	uint16_t hdr_checksum;
	uint32_t src_addr;
	uint32_t dst_addr;
};


static uint16_t
rte_ipv4_udptcp_cksum(const struct ipv4_hdr* ipv4_hdr, const void* l4_hdr)
{
	return 0; // TODO?
}

static uint16_t
rte_ipv4_cksum(const struct ipv4_hdr* ipv4_hdr)
{
	return 0; // TODO?
}

#endif
