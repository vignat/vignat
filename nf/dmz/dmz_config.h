#pragma once

#include <inttypes.h>

#include <rte_config.h>
#include <rte_ether.h>


struct dmz_config {
	// Devices
	uint16_t internet_device;
	uint16_t dmz_device;
	uint16_t intranet_device;

	// IP blocks
	uint32_t dmz_block_addr;
	uint32_t dmz_block_mask;
	uint32_t intranet_block_addr;
	uint32_t intranet_block_mask;

	// MAC addresses of devices and corresponding endpoints
	struct ether_addr device_macs[RTE_MAX_ETHPORTS];
	struct ether_addr endpoint_macs[RTE_MAX_ETHPORTS];

	// Expiration time of flows, in seconds
	uint32_t expiration_time;

	// Size of the flow table
	uint32_t max_flows;
};


void dmz_config_init(struct dmz_config* config,
                     int argc, char** argv);

void dmz_config_cmdline_print_usage(void);

void dmz_print_config(struct dmz_config* config);
