#include <inttypes.h>

// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <rte_ethdev.h>
#include <rte_mbuf.h>

#include "../lib/flowmanager.h"
#include "../lib/nf_forward.h"
#include "../lib/nf_util.h"
#include "../lib/nf_log.h"

#include "dmz_config.h"

struct dmz_config config;
struct FlowManager* internet_manager;
struct FlowManager* dmz_manager;

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

	expire_flows(internet_manager, now);
	expire_flows(dmz_manager, now);
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

	uint8_t dst_device;
	if (device == config.intranet_device) {
	} else if (device == config.dmz_device) {
	} else {
	}

	#ifdef KLEE_VERIFICATION
	klee_assert(dst_device >= 0);
	klee_assert(dst_device < RTE_MAX_ETHPORTS);
	#endif

	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];

	return dst_device;
}

void nf_config_init(int argc, char** argv) {
  dmz_config_init(&config, argc, argv);
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
