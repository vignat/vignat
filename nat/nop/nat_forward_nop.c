#include <inttypes.h>

// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <rte_ethdev.h>
#include <rte_mbuf.h>

#include "../nat_config.h"
#include "../nat_forward.h"
#include "../nat_util.h"

void
nat_core_init(struct nat_config* config)
{
	// Nothing; just mark the parameter as unused.
	(void) config;
}

uint8_t
nat_core_process(struct nat_config* config, uint8_t device, struct rte_mbuf* mbuf, uint32_t now)
{
	// Mark now as unused, we don't care about time
	(void) now;

	// This is a bit of a hack; the benchmarks are designed for a NAT, which knows where to forward packets,
	// but for a plain forwarding app without any logic, we just send all packets from LAN to the WAN port,
	// and all packets from WAN to the main LAN port, and let the recipient ignore the useless ones.

	uint8_t dst_device;
	if(device == config->wan_device) {
		dst_device = config->lan_main_device;
	} else {
		dst_device = config->wan_device;
	}

	// L2 forwarding
	struct ether_hdr* ether_header = nat_get_mbuf_ether_header(mbuf);
	ether_header->s_addr = config->device_macs[dst_device];
	ether_header->d_addr = config->endpoint_macs[dst_device];

	return dst_device;
}
