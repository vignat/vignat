#include <inttypes.h>
#include <stdbool.h>

#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "lib/stubs/rte_stubs.h"
#  include "loop.h"
#else
// DPDK uses these but doesn't include them. :|
#  include <linux/limits.h>
#  include <sys/types.h>
#  include <unistd.h>

#  include <rte_ethdev.h>
#  include <rte_ether.h>
#  include <rte_ip.h>
#  include <rte_mbuf.h>
#endif

#include "../lib/flowmanager.h"
#include "../lib/nf_forward.h"
#include "../lib/nf_util.h"
#include "../lib/nf_log.h"

#include "dmz_config.h"


enum zone {
	INTERNET,
	DMZ,
	INTRANET
};


struct dmz_config config;
struct FlowManager* internet_manager;
struct FlowManager* dmz_manager;


static enum zone get_zone(uint32_t ip) {
	if ((ip & config.dmz_block_mask) == (config.dmz_block_addr & config.dmz_block_mask)) {
		return DMZ;
	} else if ((ip & config.intranet_block_mask) == (config.intranet_block_addr & config.intranet_block_mask)) {
		return INTRANET;
	} else {
		return INTERNET;
	}
}


void nf_core_init(void)
{
        internet_manager = allocate_flowmanager(rte_eth_dev_count(),
	                                        0, // start port
                                                0, // external addr
                                                0, // WAN device
                                                config.expiration_time,
                                                config.max_flows);

        dmz_manager = allocate_flowmanager(rte_eth_dev_count(),
	                                   0, // start port
                                           0, // external addr
                                           0, // WAN device
                                           config.expiration_time,
                                           config.max_flows);

        if (internet_manager == NULL || dmz_manager == NULL) {
                rte_exit(EXIT_FAILURE, "Could not allocate flow managers");
        }
}

int nf_core_process(uint8_t device,
                    struct rte_mbuf* mbuf,
                    uint32_t now)
{
	NF_DEBUG("It is %" PRIu32, now);

	expire_flows(dmz_manager, now);
	expire_flows(internet_manager, now);
	NF_DEBUG("Flows have been expired.");

	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);

	struct ipv4_hdr* ipv4_header = nf_get_mbuf_ipv4_header(mbuf);
	if (ipv4_header == NULL) {
		NF_DEBUG("Not IPv4, dropping");
		return device;
	}

	struct tcpudp_hdr* tcpudp_header = nf_get_ipv4_tcpudp_header(ipv4_header);
	if (tcpudp_header == NULL) {
		NF_DEBUG("Not TCP/UDP, dropping");
		return device;
	}

	NF_DEBUG("Forwarding a packet from device %" PRIu8, device);

	enum zone src_zone = get_zone(ipv4_header->src_addr);
	if (src_zone == DMZ && device != config.dmz_device) {
		NF_DEBUG("IP says from DMZ, but device says no, dropping");
		return device;
	}
	if (src_zone == INTRANET && device != config.intranet_device) {
		NF_DEBUG("IP says from intranet, but device says no, dropping");
		return device;
	}
	if (src_zone == INTERNET && device != config.internet_device) {
		NF_DEBUG("IP says from internet, but device says no, dropping");
		return device;
	}

	enum zone dst_zone = get_zone(ipv4_header->dst_addr);
	if (src_zone == dst_zone) {
		NF_DEBUG("Same src/dst zones, dropping");
		return device;
	}

	if (src_zone == INTERNET && dst_zone == DMZ) {
		NF_DEBUG("INTERNET->DMZ, forwarding");
		return config.dmz_device;
	} else if (src_zone == DMZ && dst_zone == INTERNET) {
		NF_DEBUG("DMZ->INTERNET, forwarding");
		return config.internet_device;
	}

	uint8_t dst_device;
	if (src_zone == INTRANET) {
		NF_DEBUG("From Intranet");

		struct int_key key = {
			.int_src_port = tcpudp_header->src_port,
			.dst_port = tcpudp_header->dst_port,
			.int_src_ip = ipv4_header->src_addr,
			.dst_ip = ipv4_header->dst_addr,
			.int_device_id = device,
			.protocol = ipv4_header->next_proto_id
		};

		struct FlowManager* manager;
		if (dst_zone == DMZ) {
			NF_DEBUG("Towards DMZ");
			manager = dmz_manager;
			dst_device = config.dmz_device;
		} else {
			NF_DEBUG("Towards Internet");
			manager = internet_manager;
			dst_device = config.internet_device;
		}

		struct flow f;
		int flow_exists = get_flow_by_int_key(manager, &key, now, &f);
		if (!flow_exists) {
			NF_DEBUG("New flow");

			if (!allocate_flow(manager, &key, now, &f)) {
				NF_DEBUG("No space for the flow, dropping");
				return device;
			}
		}
	} else {
		NF_DEBUG("Towards Intranet");

		struct ext_key key = {
			.ext_src_port = tcpudp_header->dst_port, // intentionally swapped
			.dst_port = tcpudp_header->src_port,
			.ext_src_ip = ipv4_header->dst_addr, // switched for backwards traffic
			.dst_ip = ipv4_header->src_addr,
			.ext_device_id = device,
			.protocol = ipv4_header->next_proto_id
		};

		struct FlowManager* manager;
		if (src_zone == DMZ) {
			NF_DEBUG("From DMZ");
			manager = dmz_manager;
		} else {
			NF_DEBUG("From Internet");
			manager = internet_manager;
		}

		struct flow f;
		int flow_exists = get_flow_by_ext_key(manager, &key, now, &f);
		if (flow_exists) {
			NF_DEBUG("Found flow:");
			log_flow(&f);
		} else {
			NF_DEBUG("Unknown flow, dropping");
			return device;
		}

		dst_device = config.intranet_device;
	}

	#ifdef KLEE_VERIFICATION
	klee_assert(dst_device >= 0);
	klee_assert(dst_device < RTE_MAX_ETHPORTS);
	#endif

	NF_DEBUG("Setting MACs");
	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];

	return dst_device;
}

void nf_config_init(int argc, char** argv) {
  dmz_config_init(&config, argc, argv);
}

void nf_config_set(void* value) {
  config = *((struct dmz_config*) value);
}

void nf_config_cmdline_print_usage(void) {
  dmz_config_cmdline_print_usage();
}

void nf_print_config() {
  dmz_print_config(&config);
}

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_begin(unsigned lcore_id,
                             uint32_t time) {
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       uint32_t time) {
}

void nf_loop_iteration_end(unsigned lcore_id,
                           uint32_t time) {
}
#endif //KLEE_VERIFICATION
