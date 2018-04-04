// DPDK requires these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <stdlib.h>

#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "lib/flow.h"
#include "lib/flowmanager.h"

#include "lib/nat_config.h"
#include "lib/nf_forward.h"
#include "lib/nf_log.h"
#include "lib/nf_util.h"

struct nat_config config;
struct FlowManager* flow_manager;

void nf_core_init()
{
	flow_manager = allocate_flowmanager(
		rte_eth_dev_count(),
                config.start_port,
                config.external_addr,
                config.wan_device,
                config.expiration_time,
                config.max_flows
	);

	if (flow_manager == NULL) {
		rte_exit(EXIT_FAILURE, "Could not allocate flow manager");
	}
}

int nf_core_process(struct rte_mbuf* mbuf, time_t now)
{
	NF_DEBUG("It is %" PRIu32, now);

	expire_flows(flow_manager, now);
	NF_DEBUG("Flows have been expired");

	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

	struct ipv4_hdr* ipv4_header = nf_get_mbuf_ipv4_header(mbuf);
	if (ipv4_header == NULL) {
		NF_DEBUG("Not IPv4, dropping");
		return mbuf->port;
	}

	struct tcpudp_hdr* tcpudp_header = nf_get_ipv4_tcpudp_header(ipv4_header);
	if (tcpudp_header == NULL) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return mbuf->port;
	}

	NF_DEBUG("Forwarding an IPv4 packet on device %" PRIu16, mbuf->port);

	uint16_t dst_device;
	if (mbuf->port == config.wan_device) {
		NF_DEBUG("Device %" PRIu16 " is external", mbuf->port);

		struct ext_key key = {
			.ext_src_port = tcpudp_header->dst_port, //intentionally swapped.
			.dst_port = tcpudp_header->src_port,
			.ext_src_ip = ipv4_header->dst_addr, //Note, they are switched for
			.dst_ip = ipv4_header->src_addr, // the backwards traffic
			.ext_device_id = mbuf->port,
			.protocol = ipv4_header->next_proto_id
		};

		NF_DEBUG("For key:");
		log_ext_key(&key);

		struct flow f;
		int flow_exists = get_flow_by_ext_key(flow_manager, &key, now, &f);
		if (flow_exists) {
			NF_DEBUG("Found flow:");
			log_flow(&f);

			ipv4_header->dst_addr = f.int_src_ip;
			tcpudp_header->dst_port = f.int_src_port;
			dst_device = f.int_device_id;
		} else {
			NF_DEBUG("Unknown flow, dropping");
			return mbuf->port;
		}
	} else {
		NF_DEBUG("Device %" PRIu16 " is internal (not %" PRIu16 ")", mbuf->port, config.wan_device);

		struct int_key key = {
			.int_src_port = tcpudp_header->src_port,
			.dst_port = tcpudp_header->dst_port,
			.int_src_ip = ipv4_header->src_addr,
			.dst_ip = ipv4_header->dst_addr,
			.int_device_id = mbuf->port,
			.protocol = ipv4_header->next_proto_id
		};

		NF_DEBUG("For key:");
		log_int_key(&key);

		struct flow f;
		int flow_exists = get_flow_by_int_key(flow_manager, &key, now, &f);
		if (!flow_exists) {
			NF_DEBUG("New flow");

			if (!allocate_flow(flow_manager, &key, now, &f)) {
				NF_DEBUG("No space for the flow, dropping");
				return mbuf->port;
			}
		}

		NF_DEBUG("Forwarding to:");
		log_flow(&f);

		ipv4_header->src_addr = f.ext_src_ip;
		tcpudp_header->src_port = f.ext_src_port;
		dst_device = f.ext_device_id;
	}

	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];
	nf_set_ipv4_checksum(ipv4_header);

	return dst_device;
}


void nf_config_init(int argc, char** argv) {
  nat_config_init(&config, argc, argv);
}

void nf_config_cmdline_print_usage(void) {
  nat_config_cmdline_print_usage();
}

void nf_print_config() {
  nat_print_config(&config);
}

#ifdef KLEE_VERIFICATION
#include "loop.h"

void nf_loop_iteration_begin(unsigned lcore_id,
                             time_t time) {
  loop_iteration_begin(get_dmap_pp(flow_manager), get_dchain_pp(flow_manager),
                       lcore_id, time,
                       config.max_flows,
                       config.start_port);
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       time_t time) {
  loop_iteration_assumptions(get_dmap_pp(flow_manager), get_dchain_pp(flow_manager),
                             lcore_id, time,
                             config.max_flows,
                             config.start_port);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           time_t time) {
  loop_iteration_end(get_dmap_pp(flow_manager), get_dchain_pp(flow_manager),
                     lcore_id, time,
                     config.max_flows,
                     config.start_port);
}
#endif

