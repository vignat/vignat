#include <inttypes.h>
#include <stdbool.h>

// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <rte_common.h>
#include <rte_ethdev.h>
#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

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

int nf_core_process(struct rte_mbuf* mbuf, time_t now)
{
	NF_DEBUG("It is %" PRIu32, now);

	expire_flows(dmz_manager, now);
	expire_flows(internet_manager, now);
	NF_DEBUG("Flows have been expired.");

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

	NF_DEBUG("Forwarding a packet from device %" PRIu16, mbuf->port);

	enum zone src_zone = get_zone(ipv4_header->src_addr);
	if (src_zone == DMZ && mbuf->port != config.dmz_device) {
		NF_DEBUG("IP says from DMZ, but device says no, dropping");
		return mbuf->port;
	}
	if (src_zone == INTRANET && mbuf->port != config.intranet_device) {
		NF_DEBUG("IP says from intranet, but device says no, dropping");
		return mbuf->port;
	}
	if (src_zone == INTERNET && mbuf->port != config.internet_device) {
		NF_DEBUG("IP says from internet, but device says no, dropping");
		return mbuf->port;
	}

	enum zone dst_zone = get_zone(ipv4_header->dst_addr);
	if (src_zone == dst_zone) {
		NF_DEBUG("Same src/dst zones, dropping");
		return mbuf->port;
	}

	if (src_zone == INTERNET && dst_zone == DMZ) {
		NF_DEBUG("INTERNET->DMZ, forwarding");
		return config.dmz_device;
	} else if (src_zone == DMZ && dst_zone == INTERNET) {
		NF_DEBUG("DMZ->INTERNET, forwarding");
		return config.internet_device;
	}

	uint16_t dst_device;
	if (src_zone == INTRANET) {
		NF_DEBUG("From Intranet");

		struct int_key key = {
			.int_src_port = tcpudp_header->src_port,
			.dst_port = tcpudp_header->dst_port,
			.int_src_ip = ipv4_header->src_addr,
			.dst_ip = ipv4_header->dst_addr,
			.int_device_id =  1, // see remark in the else block
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
				return mbuf->port;
			}
		}
	} else {
		NF_DEBUG("Towards Intranet");

		// This is, clearly, an *external* flow.
		// However, the flow manager is designed for a NAT.
		// In a NAT, external flows have the NAT IP as their destination,
		// whereas a DMZ performs no translation thus the destination is the target IP.
		// Therefore, we treat all flows as internal from the flow manager's point of view.
		// All we have to do is swap the src/dst... so basically we're using it as a single map.
		// We also ignore the device, since there is only 1 on each side per flow manager.
		// (but the device has to be != 0, flows expect to have different int/ext devices)
		// TODO: Just use the map directly. Perhaps extract flow management ouf of the manager.
		struct int_key key = {
			.int_src_port = tcpudp_header->dst_port,
			.dst_port = tcpudp_header->src_port,
			.int_src_ip = ipv4_header->dst_addr,
			.dst_ip = ipv4_header->src_addr,
			.int_device_id = 1,
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
		int flow_exists = get_flow_by_int_key(manager, &key, now, &f);
		if (flow_exists) {
			NF_DEBUG("Found flow:");
			log_flow(&f);
		} else {
			NF_DEBUG("Unknown flow, dropping");
			return mbuf->port;
		}

		dst_device = config.intranet_device;
	}

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
#include "dmz_loop.h"
void nf_loop_iteration_begin(unsigned lcore_id,
                             time_t time) {
	dmz_loop_iteration_begin(get_dchain_pp(internet_manager), get_dchain_pp(dmz_manager),
				 get_dmap_pp(internet_manager), get_dmap_pp(dmz_manager),
				 time,
				 config.max_flows);
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       time_t time) {
	dmz_loop_iteration_assumptions(get_dchain_pp(internet_manager), get_dchain_pp(dmz_manager),
				       get_dmap_pp(internet_manager), get_dmap_pp(dmz_manager),
				       time,
				       config.max_flows);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           time_t time) {
	dmz_loop_iteration_end(get_dchain_pp(internet_manager), get_dchain_pp(dmz_manager),
			       get_dmap_pp(internet_manager), get_dmap_pp(dmz_manager),
			       time,
			       config.max_flows);
}
#endif //KLEE_VERIFICATION
