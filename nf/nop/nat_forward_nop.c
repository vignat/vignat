// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <rte_ethdev.h>
#include <rte_mbuf.h>

#include "../lib/nat_config.h"
#include "../lib/nf_forward.h"
#include "../lib/nf_util.h"

struct nat_config config;

void nf_core_init(void)
{
}

int nf_core_process(struct rte_mbuf* mbuf, time_t now)
{
	// Mark now as unused, we don't care about time
	(void) now;

	// This is a bit of a hack; the benchmarks are designed for a NAT, which knows where to forward packets,
	// but for a plain forwarding app without any logic, we just send all packets from LAN to the WAN port,
	// and all packets from WAN to the main LAN port, and let the recipient ignore the useless ones.

	uint8_t dst_device;
	if(mbuf->port == config.wan_device) {
		dst_device = config.lan_main_device;
	} else {
		dst_device = config.wan_device;
	}

	// L2 forwarding
	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);
	ether_header->s_addr = config.device_macs[dst_device];
	ether_header->d_addr = config.endpoint_macs[dst_device];

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
