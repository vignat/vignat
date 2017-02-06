#include <inttypes.h>

#include <netinet/in.h>

#include "lib/stubs/rte_stubs.h"

#include "../nat_util.h"


struct ether_hdr*
nat_get_mbuf_ether_header(struct rte_mbuf* mbuf)
{
	return rte_pktmbuf_mtod(mbuf, struct ether_hdr*);
}

struct ipv4_hdr*
nat_get_mbuf_ipv4_header(struct rte_mbuf* mbuf)
{
	struct ether_hdr* ether_header = nat_get_mbuf_ether_header(mbuf);
	if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) && !(mbuf->packet_type == 0 && ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))) {
		return NULL;
	}

	return rte_pktmbuf_mtod_offset(mbuf, struct ipv4_hdr*, sizeof(struct ether_hdr));
}

struct tcpudp_hdr*
nat_get_ipv4_tcpudp_header(struct ipv4_hdr* header)
{
	if (header->next_proto_id != IPPROTO_TCP && header->next_proto_id != IPPROTO_UDP) {
		return NULL;
	}

	uint8_t offset = header->version_ihl & IPV4_HDR_IHL_MASK;
	// TODO use offset
	return (struct tcpudp_hdr*)(header + 1);
}

void
nat_set_ipv4_checksum(struct ipv4_hdr* header)
{
	// TODO: See if can be Offloaded to hardware
	// TODO: Replicate Luis' work here
	header->hdr_checksum = 0;

	if (header->next_proto_id == IPPROTO_TCP) {
		struct tcp_hdr* tcp_header = (struct tcp_hdr*)(header + 1);
		tcp_header->cksum = 0;
		tcp_header->cksum = rte_ipv4_udptcp_cksum(header, tcp_header);
	} else if (header->next_proto_id == IPPROTO_UDP) {
		struct udp_hdr * udp_header = (struct udp_hdr*)(header + 1);
		udp_header->dgram_cksum = 0;
		udp_header->dgram_cksum = rte_ipv4_udptcp_cksum(header, udp_header);
	}

	header->hdr_checksum = rte_ipv4_cksum(header);
}

// no *_to_str, don't need them
