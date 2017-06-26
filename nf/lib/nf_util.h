#pragma once

#include <inttypes.h>

// rte_mbuf
struct rte_mbuf;

// rte_ether
struct ether_hdr;

// rte_ip
struct ipv4_hdr;


// A header for TCP or UDP packets, containing common data.
// (This is used to point into DPDK data structures!)
struct tcpudp_hdr {
	uint16_t src_port;
	uint16_t dst_port;
} __attribute__((__packed__));


struct ether_hdr* nf_get_mbuf_ether_header(struct rte_mbuf* mbuf);

// TODO for consistency it'd be nice if this took an ether_hdr as argument, or if they all took rte_mbuf
struct ipv4_hdr* nf_get_mbuf_ipv4_header(struct rte_mbuf* mbuf);

struct tcpudp_hdr* nf_get_ipv4_tcpudp_header(struct ipv4_hdr* header);

void nf_set_ipv4_checksum(struct ipv4_hdr* header);

uintmax_t nf_util_parse_int(const char* str, const char* name,
                            int base, char next);
char* nf_mac_to_str(struct ether_addr* addr);

char* nf_ipv4_to_str(uint32_t addr);
