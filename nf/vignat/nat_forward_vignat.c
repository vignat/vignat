#include <inttypes.h>

#ifdef KLEE_VERIFICATION
#  include <klee/klee.h>
#  include "lib/stubs/rte_stubs.h"
#  include "loop.h"
#else
// DPDK requires these but doesn't include them. :|
#  include <linux/limits.h>
#  include <sys/types.h>
#  include <unistd.h>

#  include <rte_ethdev.h>
#  include <rte_ether.h>
#  include <rte_ip.h>
#  include <rte_mbuf.h>
#endif

#include "lib/flow.h"
#include "flowmanager.h"

#include "lib/nat_config.h"
#include "lib/nf_forward.h"
#include "lib/nf_log.h"
#include "lib/nf_util.h"

struct nat_config config;

void nf_core_init()
{
	if (!allocate_flowmanager(rte_eth_dev_count(),
                            config.start_port,
                            config.external_addr,
                            config.wan_device,
                            config.expiration_time,
                            config.max_flows)) {
		rte_exit(EXIT_FAILURE, "Could not allocate flow manager");
	}
}

int nf_core_process(uint8_t device,
                    struct rte_mbuf* mbuf,
                    uint32_t now)
{
	NF_DEBUG("It is %" PRIu32, now);

	expire_flows(now);
	NF_DEBUG("Flows have been expired");

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

	NF_DEBUG("Forwarding an IPv4 packet on device %" PRIu8, device);

	uint8_t dst_device;
  int allocated = 0;
	if (device == config.wan_device) {
		NF_DEBUG("Device %" PRIu8 " is external", device);

		struct ext_key key = {
			.ext_src_port = tcpudp_header->dst_port, //intentionally swapped.
			.dst_port = tcpudp_header->src_port,
			.ext_src_ip = ipv4_header->dst_addr, //Note, they are switched for
			.dst_ip = ipv4_header->src_addr, // the backwards traffic
			.ext_device_id = device,
			.protocol = ipv4_header->next_proto_id
		};

		NF_DEBUG("For key:");
		log_ext_key(&key);

		struct flow f;
		int flow_exists = get_flow_by_ext_key(&key, now, &f);
		if (flow_exists) {
			NF_DEBUG("Found flow:");
			log_flow(&f);

			ipv4_header->dst_addr = f.int_src_ip;
			tcpudp_header->dst_port = f.int_src_port;
			dst_device = f.int_device_id;
      //klee_assert(f.ik.int_device_id == f.int_device_id);
      //klee_assert(f.ek.ext_device_id == f.ext_device_id);
      //klee_assert(f.int_device_id != f.ext_device_id);
      allocated = 1;
		} else {
			NF_DEBUG("Unknown flow, dropping");
			return device;
		}
	} else {
		NF_DEBUG("Device %" PRIu8 " is internal (not %" PRIu8 ")", device, config.wan_device);

		struct int_key key = {
			.int_src_port = tcpudp_header->src_port,
			.dst_port = tcpudp_header->dst_port,
			.int_src_ip = ipv4_header->src_addr,
			.dst_ip = ipv4_header->dst_addr,
			.int_device_id = device,
			.protocol = ipv4_header->next_proto_id
		};

		NF_DEBUG("For key:");
		log_int_key(&key);

		struct flow f;
		int flow_exists = get_flow_by_int_key(&key, now, &f);
		if (!flow_exists) {
			NF_DEBUG("New flow");

			if (!allocate_flow(&key, now, &f)) {
				NF_DEBUG("No space for the flow, dropping");
				return device;
			}
		}

		NF_DEBUG("Forwarding to:");
		log_flow(&f);

		ipv4_header->src_addr = f.ext_src_ip;
		tcpudp_header->src_port = f.ext_src_port;
		dst_device = f.ext_device_id;
    //klee_assert(f.ik.int_device_id == f.int_device_id);
    //klee_assert(f.ek.ext_device_id == f.ext_device_id);
    //klee_assert(f.int_device_id != f.ext_device_id);
    allocated = 1;
	}

	#ifdef KLEE_VERIFICATION
		klee_assert(dst_device >= 0);
		klee_assert(dst_device < RTE_MAX_ETHPORTS);
	#endif

	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];

	nf_set_ipv4_checksum(ipv4_header);

  //klee_assert(allocated);
  //klee_assert(device != dst_device);
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

void nf_loop_iteration_begin(unsigned lcore_id,
                             uint32_t time) {
	loop_iteration_begin(get_dmap_pp(), get_dchain_pp(),
                       lcore_id, time,
                       config.max_flows,
                       config.start_port);
}

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       uint32_t time) {
  loop_iteration_assumptions(get_dmap_pp(), get_dchain_pp(),
                             lcore_id, time,
                             config.max_flows,
                             config.start_port);
}

void nf_loop_iteration_end(unsigned lcore_id,
                           uint32_t time) {
  loop_iteration_end(get_dmap_pp(), get_dchain_pp(),
                     lcore_id, time,
                     config.max_flows,
                     config.start_port);
}

#endif //KLEE_VERIFICATION

