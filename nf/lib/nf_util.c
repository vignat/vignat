#include <inttypes.h>

#include <netinet/in.h>

#ifdef KLEE_VERIFICATION
#  include "stubs/rte_stubs.h"
#else//KLEE_VERIFICATION
#  include <rte_byteorder.h>
#  include <rte_ether.h>
#  include <rte_ip.h>
#  include <rte_mbuf.h>
#  include <rte_tcp.h>
#  include <rte_udp.h>
#endif//KLEE_VERIFICATION

#include "nf_util.h"


struct ether_hdr*
nf_get_mbuf_ether_header(struct rte_mbuf* mbuf)
{
	return rte_pktmbuf_mtod(mbuf, struct ether_hdr*);
}

// TODO for consistency it'd be nice if this took an ether_hdr as argument, or if they all took rte_mbuf
struct ipv4_hdr*
nf_get_mbuf_ipv4_header(struct rte_mbuf* mbuf)
{
	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);
	if (!RTE_ETH_IS_IPV4_HDR(mbuf->packet_type) &&
      !(mbuf->packet_type == 0 &&
        ether_header->ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))) {
		return NULL;
	}

	return rte_pktmbuf_mtod_offset(mbuf, struct ipv4_hdr*, sizeof(struct ether_hdr));
}

struct tcpudp_hdr*
nf_get_ipv4_tcpudp_header(struct ipv4_hdr* header)
{
	if (header->next_proto_id != IPPROTO_TCP &&
      header->next_proto_id != IPPROTO_UDP) {
		return NULL;
	}

	uint8_t offset = header->version_ihl & IPV4_HDR_IHL_MASK;
	// TODO use offset
	return (struct tcpudp_hdr*)(header + 1);
}

void
nf_set_ipv4_checksum(struct ipv4_hdr* header)
{
	// TODO: See if can be offloaded to hardware
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

uintmax_t nf_util_parse_int(const char* str, const char* name,
                            int base, char next) {
  char* temp;
  intmax_t result = strtoimax(str, &temp, base);

  // There's also a weird failure case with overflows, but let's not care
  if(temp == str || *temp != next) {
    rte_exit(EXIT_FAILURE, "Error while parsing '%s': %s\n", name, str);
  }

  return result;
}

char*
nf_mac_to_str(struct ether_addr* addr)
{
	// format is xx:xx:xx:xx:xx:xx\0
	uint16_t buffer_size = 6 * 2 + 5 + 1;
	char* buffer = (char*) calloc(buffer_size, sizeof(char));
	if (buffer == NULL) {
		rte_exit(EXIT_FAILURE, "Out of memory in nf_mac_to_str!");
	}

	ether_format_addr(buffer, buffer_size, addr);
	return buffer;
}

char*
nf_ipv4_to_str(uint32_t addr)
{
	// format is xxx.xxx.xxx.xxx\0
	uint16_t buffer_size = 4 * 3 + 3 + 1;
	char* buffer = (char*) calloc(buffer_size, sizeof(char));
	if (buffer == NULL) {
		rte_exit(EXIT_FAILURE, "Out of memory in nf_ipv4_to_str!");
	}

	snprintf(buffer, buffer_size, "%" PRIu8 ".%" PRIu8 ".%" PRIu8 ".%" PRIu8,
		 addr        & 0xFF,
		(addr >>  8) & 0xFF,
		(addr >> 16) & 0xFF,
		(addr >> 24) & 0xFF
	);
	return buffer;
}
