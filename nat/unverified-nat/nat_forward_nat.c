// This file is a C++ file masquerading as a C file,
// as DPDK's makefiles do *not* like C++ files at all.
// If you rename this to a .cc or .cpp, g++ will not find it.

#include <inttypes.h>
#include <stdlib.h>
#include <time.h>

#include <queue>
#include <vector>

#include <rte_ethdev.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "../nat_config.h"
#include "../nat_forward.h"
#include "../nat_log.h"
#include "../nat_util.h"

#include "nat_flow.h"
#include "nat_map.h"

// ICMP support is not implemented, as this NAT only exists for benchmarking purposes;
// since the protocol type has to be checked anyway, an ICMP check would not significantly
// change performance.


static bool
nat_flow_greater_timestamp(nat_flow* left, nat_flow* right)
{
	return left->last_packet_timestamp > right->last_packet_timestamp;
}


static std::vector<uint16_t> available_ports;

static struct nat_map* flows_from_inside;
static struct nat_map* flows_from_outside;

static std::priority_queue<struct nat_flow*,
				std::vector<struct nat_flow*>,
				decltype(&nat_flow_greater_timestamp)> flows_by_time(nat_flow_greater_timestamp);

static uint32_t current_timestamp;


static struct nat_flow_id
nat_flow_id_from_ipv4(struct ipv4_hdr* header)
{
	struct tcpudp_hdr* tcpudp_header = nat_get_ipv4_tcpudp_header(header);

	nat_flow_id id;
	id.src_addr = header->src_addr;
	id.src_port = tcpudp_header->src_port;
	id.dst_addr = header->dst_addr;
	id.dst_port = tcpudp_header->dst_port;
	id.protocol = header->next_proto_id;
	return id;
}


static void
nat_flows_by_time_refresh(void)
{
	// This only works because the default container of priority_queue is a vector.
	std::make_heap(
		const_cast<nat_flow**>(&flows_by_time.top()),
		const_cast<nat_flow**>(&flows_by_time.top()) + flows_by_time.size(),
		nat_flow_greater_timestamp
	);
}


void
nat_core_init(struct nat_config* config)
{
  int power = 1;
  while(power < config->max_flows)
    power*=2;
	nat_map_set_fns(&nat_flow_id_hash, &nat_flow_id_eq);
	flows_from_inside = nat_map_create(power);
	flows_from_outside = nat_map_create(power);

	// uint32_t for the port as max_flows is 1-based and thus may be 2^16.
	for (uint32_t port = 0; port < config->max_flows; port++) {
		available_ports.push_back((uint16_t) port + config->start_port);
	}

	current_timestamp = 0;

	NAT_DEBUG("Initialized");
}

uint8_t
nat_core_process(struct nat_config* config, uint8_t device, struct rte_mbuf* mbuf, uint32_t now)
{
	// Set this iteration's time
	NAT_DEBUG("It is %" PRIu32, now);

	// Expire flows if needed
	if (now > current_timestamp && !flows_by_time.empty()) {
		nat_flows_by_time_refresh();

		nat_flow* expired_flow = flows_by_time.top();
		while ((current_timestamp - expired_flow->last_packet_timestamp) > config->expiration_time) {
			struct nat_flow_id expired_from_outside;
			expired_from_outside.src_addr = expired_flow->id.dst_addr;
			expired_from_outside.src_port = expired_flow->id.dst_port;
			expired_from_outside.dst_addr = config->external_addr;
			expired_from_outside.dst_port = expired_flow->external_port;
			expired_from_outside.protocol = expired_flow->id.protocol;

			available_ports.push_back(expired_flow->external_port);
			nat_map_remove(flows_from_inside, expired_flow->id);
			nat_map_remove(flows_from_outside, expired_from_outside);
			flows_by_time.pop();

			NAT_DEBUG("Expiring %" PRIu16 " -> %" PRIu16 "\n", expired_flow->id.src_port, expired_flow->id.dst_port);

			free(expired_flow);

			expired_flow = flows_by_time.top();
		}
	}

	current_timestamp = now;


	// Redirect packets
	if (device == config->wan_device) {
		NAT_DEBUG("External packet");

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

		struct nat_flow_id flow_id = nat_flow_id_from_ipv4(ipv4_header);
		NAT_DEBUG("Flow: %" PRIu16 " -> %" PRIu16, flow_id.src_port, flow_id.dst_port);

		struct nat_flow* flow;
		if (!nat_map_get(flows_from_outside, flow_id, &flow)) {
			NAT_DEBUG("Unknown flow, dropping");
			return device;
		}

		// Refresh
		flow->last_packet_timestamp = current_timestamp;

		// L2 forwarding
		struct ether_hdr* ether_header = nat_get_mbuf_ether_header(mbuf);
		ether_header->s_addr = config->device_macs[flow->internal_device];
		ether_header->d_addr = config->endpoint_macs[flow->internal_device];

		// L3 forwarding
		ipv4_header->dst_addr = flow->id.src_addr;
		tcpudp_header->dst_port = flow->id.src_port;

		// Checksum
		nat_set_ipv4_checksum(ipv4_header);

		return flow->internal_device;
	} else {
		NAT_DEBUG("Internal packet");

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

		struct nat_flow_id flow_id = nat_flow_id_from_ipv4(ipv4_header);
		NAT_DEBUG("Flow: %" PRIu16 " -> %" PRIu16, flow_id.src_port, flow_id.dst_port);

		struct nat_flow* flow;
		if (!nat_map_get(flows_from_inside, flow_id, &flow)) {
			if (available_ports.empty()) {
				NAT_DEBUG("No available ports, dropping");
				return device;
			}

			uint16_t flow_port = available_ports.back();
			available_ports.pop_back();

			flow = (nat_flow*) malloc(sizeof(nat_flow));
			if (flow == NULL) {
				rte_exit(EXIT_FAILURE, "Out of memory, can't create a flow!");
			}

			flow->id = flow_id;
			flow->external_port = flow_port;
			flow->internal_device = device;
			flow->last_packet_timestamp = 0;

			struct nat_flow_id flow_from_outside;
			flow_from_outside.src_addr = ipv4_header->dst_addr;
			flow_from_outside.src_port = tcpudp_header->dst_port;
			flow_from_outside.dst_addr = config->external_addr;
			flow_from_outside.dst_port = flow_port;
			flow_from_outside.protocol = ipv4_header->next_proto_id;

			NAT_DEBUG("Creating flow, port=%" PRIu16, flow_port);

			nat_map_insert(flows_from_inside, flow_id, flow);
			nat_map_insert(flows_from_outside, flow_from_outside, flow);
			flows_by_time.push(flow);
		}

		// Refresh
		flow->last_packet_timestamp = current_timestamp;

		// L2 forwarding
		struct ether_hdr* ether_header = nat_get_mbuf_ether_header(mbuf);
		ether_header->s_addr = config->device_macs[config->wan_device];
		ether_header->d_addr = config->endpoint_macs[config->wan_device];

		// L3 forwarding
		ipv4_header->src_addr = config->external_addr;
		tcpudp_header->src_port = flow->external_port;

		// Checksum
		nat_set_ipv4_checksum(ipv4_header);

		return config->wan_device;
	}
}
