#include <inttypes.h>

#if KLEE_VERIFICATION
	#include <klee/klee.h>
	#include "lib/stubs/rte_stubs.h"
#else
	// DPDK requires these but doesn't include them. :|
	#include <linux/limits.h>
	#include <sys/types.h>
	#include <unistd.h>

	#include <rte_ethdev.h>
	#include <rte_ether.h>
	#include <rte_ip.h>
	#include <rte_mbuf.h>
#endif

#include "lib/flow.h"
#include "lib/flowmanager.h"

#include "../nat_config.h"
#include "../nat_forward.h"
#include "../nat_log.h"
#include "../nat_util.h"


void
nat_core_init(struct nat_config* config)
{
	if (!allocate_flowmanager(rte_eth_dev_count(), config->start_port, config->external_addr, config->wan_device, config->expiration_time, config->max_flows)) {
		rte_exit(EXIT_FAILURE, "Could not allocate flow manager");
	}
}

uint8_t
nat_core_process(struct nat_config* config, uint8_t device, struct rte_mbuf* mbuf, uint32_t now)
{
	NAT_DEBUG("It is %" PRIu32, now);

	expire_flows(now);
	NAT_DEBUG("Flows have been expired");

	struct ether_hdr* ether_header = nat_get_mbuf_ether_header(mbuf);

	struct ipv4_hdr* ipv4_header = nat_get_mbuf_ipv4_header(mbuf);
	if (ipv4_header == NULL) {
		NAT_DEBUG("Not IPv4, dropping");
		return device;
	}

	struct tcpudp_hdr* tcpudp_header = nat_get_ipv4_tcpudp_header(ipv4_header);
	if (tcpudp_header == NULL) {
		NAT_DEBUG("Not TCP/UDP, dropping");
		return device;
	}

	NAT_DEBUG("Forwarding an IPv4 packet on device %" PRIu8, device);

	uint8_t dst_device;
	if (device == config->wan_device) {
		NAT_DEBUG("Device %" PRIu8 " is external", device);

		struct ext_key key = {
			.ext_src_port = tcpudp_header->dst_port, //intentionally swapped.
			.dst_port = tcpudp_header->src_port,
			.ext_src_ip = ipv4_header->dst_addr, //Note, they are switched for
			.dst_ip = ipv4_header->src_addr, // the backwards traffic
			.ext_device_id = device,
			.protocol = ipv4_header->next_proto_id
		};

		NAT_DEBUG("For key:");
		log_ext_key(&key);

		struct flow f;
		int flow_exists = get_flow_by_ext_key(&key, now, &f);
		if (flow_exists) {
			NAT_DEBUG("Found flow:");
			log_flow(&f);

			ipv4_header->dst_addr = f.int_src_ip;
			tcpudp_header->dst_port = f.int_src_port;
			dst_device = f.int_device_id;
		} else {
			NAT_DEBUG("Unknown flow, dropping");
			return device;
		}
	} else {
		NAT_DEBUG("Device %" PRIu8 " is internal (not %" PRIu8 ")", device, config->wan_device);

		struct int_key key = {
			.int_src_port = tcpudp_header->src_port,
			.dst_port = tcpudp_header->dst_port,
			.int_src_ip = ipv4_header->src_addr,
			.dst_ip = ipv4_header->dst_addr,
			.int_device_id = device,
			.protocol = ipv4_header->next_proto_id
		};

		NAT_DEBUG("For key:");
		log_int_key(&key);

		struct flow f;
		int flow_exists = get_flow_by_int_key(&key, now, &f);
		if (!flow_exists) {
			NAT_DEBUG("New flow");

			if (!allocate_flow(&key, now, &f)) {
				NAT_DEBUG("No space for the flow, dropping");
				return device;
			}
		}

		NAT_DEBUG("Forwarding to:");
		log_flow(&f);

		ipv4_header->src_addr = f.ext_src_ip;
		tcpudp_header->src_port = f.ext_src_port;
		dst_device = f.ext_device_id;
	}

	#ifdef KLEE_VERIFICATION
		klee_assert(dst_device >= 0);
		klee_assert(dst_device < RTE_MAX_ETHPORTS);
	#endif

	ether_header->s_addr = config->device_macs[dst_device];
	ether_header->d_addr = config->endpoint_macs[dst_device];

	nat_set_ipv4_checksum(ipv4_header);

	return dst_device;
}
