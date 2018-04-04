#include <getopt.h>
#include <inttypes.h>
#include <stdlib.h>

// DPDK needs these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_config.h>
#include <rte_ethdev.h>

#include <cmdline_parse_etheraddr.h>
#include <cmdline_parse_ipaddr.h>

#include "dmz_config.h"
#include "../lib/nf_util.h"
#include "../lib/nf_log.h"


#define PARSE_ERROR(format, ...) \
		dmz_config_cmdline_print_usage(); \
		rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);


static uintmax_t
dmz_config_parse_int(const char* str, const char* name, int base, char next)
{
	char* temp;
	intmax_t result = strtoimax(str, &temp, base);

	// There's also a weird failure case with overflows, but let's not care
	if(temp == str || *temp != next) {
		rte_exit(EXIT_FAILURE, "Error while parsing '%s': %s\n", name, str);
	}

	return result;
}

static uint32_t
dmz_config_parse_ipv4(const char* str, const char* name)
{
	struct cmdline_token_ipaddr tk;
	tk.ipaddr_data.flags = CMDLINE_IPADDR_V4;

	struct cmdline_ipaddr res;
	if (cmdline_parse_ipaddr((cmdline_parse_token_hdr_t*) &tk, str, &res, sizeof(res)) < 0) {
		PARSE_ERROR("Error while parsing '%s': %s\n", name, str);
	}

	return res.addr.ipv4.s_addr;
}

void dmz_config_init(struct dmz_config* config,
                     int argc, char** argv)
{
	unsigned nb_devices = rte_eth_dev_count();
	struct option long_options[] = {
		{"inter-dev",		required_argument,	NULL, 'a'},
		{"dmz-dev",		required_argument,	NULL, 'b'},
		{"intra-dev",		required_argument,	NULL, 'c'},
		{"dmz-addr",		required_argument,	NULL, 'f'},
		{"dmz-mask",		required_argument,	NULL, 'g'},
		{"intra-addr",		required_argument,	NULL, 'h'},
		{"intra-mask",		required_argument,	NULL, 'i'},
		{"eth-dest",		required_argument,	NULL, 'j'},
		{"expire",		required_argument,	NULL, 'k'},
		{"max-flows",		required_argument,	NULL, 'l'},
		{NULL, 			0,			NULL, 0  }
	};

	// Set the devices' own MACs
	for (uint16_t device = 0; device < nb_devices; device++) {
		rte_eth_macaddr_get(device, &(config->device_macs[device]));
	}

	int opt;
	while ((opt = getopt_long(argc, argv, "a:b:c:d:e:f:g:h:i:j:k:l:", long_options, NULL)) != EOF) {
		unsigned device;
		switch (opt) {
			case 'a':
				config->internet_device = dmz_config_parse_int(optarg, "internet device", 10, '\0');
				if (config->internet_device >= nb_devices) {
					PARSE_ERROR("internet device: %d >= nb_devices (%d)\n", config->internet_device, nb_devices);
				}
				break;

			case 'b':
				config->dmz_device = dmz_config_parse_int(optarg, "dmz device", 10, '\0');
				if (config->dmz_device >= nb_devices) {
					PARSE_ERROR("dmz device: %d >= nb_devices (%d)\n", config->dmz_device, nb_devices);
				}
				break;

			case 'c':
				config->intranet_device = dmz_config_parse_int(optarg, "intranet device", 10, '\0');
				if (config->intranet_device >= nb_devices) {
					PARSE_ERROR("intranet device: %d >= nb_devices (%d)\n", config->intranet_device, nb_devices);
				}
				break;

			case 'f':
				config->dmz_block_addr = dmz_config_parse_ipv4(optarg, "dmz addr");
				break;
			case 'g':
				config->dmz_block_mask = dmz_config_parse_ipv4(optarg, "dmz mask");
				break;

			case 'h':
				config->intranet_block_addr = dmz_config_parse_ipv4(optarg, "intranet addr");
				break;
			case 'i':
				config->intranet_block_mask = dmz_config_parse_ipv4(optarg, "intranet mask");
				break;

			case 'j':
				device = dmz_config_parse_int(optarg, "eth-dest device", 10, ',');
				if (device >= nb_devices) {
					PARSE_ERROR("eth-dest: device %d >= nb_devices (%d)\n", device, nb_devices);
				}

				optarg += 2;
				if (cmdline_parse_etheraddr(NULL, optarg, &(config->endpoint_macs[device]), sizeof(int64_t)) < 0) {
					PARSE_ERROR("Invalid MAC address: %s\n", optarg);
				}
				break;

			case 'k':
				config->expiration_time = dmz_config_parse_int(optarg, "exp-time", 10, '\0');
				if (config->expiration_time == 0) {
					PARSE_ERROR("Expiration time must be strictly positive.\n");
				}
				break;

			case 'l':
				config->max_flows = dmz_config_parse_int(optarg, "max-flows", 10, '\0');
				if (config->max_flows <= 0) {
					PARSE_ERROR("Flow table size must be strictly positive.\n");
				}
				break;
		}
	}

	// Reset getopt
	optind = 1;
}

void dmz_config_cmdline_print_usage(void)
{
	NF_INFO("Usage:\n"
		"[DPDK EAL options] --\n"
		"\t--eth-dest <device>,<mac>: MAC address of the endpoint linked to a device.\n"
		"\t--expire <time>: flow expiration time.\n"
		"\t--{inter,dmz,intra}-dev <device>: set device.\n"
		"\t--{dmz,intra}-addr <addr>: set block address.\n"
		"\t--{dmz,intra}-mask <mask>: set block mask.\n"
		"\t--max-flows <n>: flow table capacity.\n"
	);
}

void dmz_print_config(struct dmz_config* config)
{
	NF_INFO("\n--- DMZ Config ---\n");

	NF_INFO("Internet device: %" PRIu8, config->internet_device);
	NF_INFO("DMZ device: %" PRIu8, config->dmz_device);
	NF_INFO("Intranet device: %" PRIu8, config->intranet_device);

	char* dmz_addr_str = nf_ipv4_to_str(config->dmz_block_addr);
	char* dmz_mask_str = nf_ipv4_to_str(config->dmz_block_mask);
	NF_INFO("DMZ block address: %s", dmz_addr_str);
	NF_INFO("DMZ block mask: %s", dmz_mask_str);
	free(dmz_addr_str);
	free(dmz_mask_str);

	char* intra_addr_str = nf_ipv4_to_str(config->intranet_block_addr);
	char* intra_mask_str = nf_ipv4_to_str(config->intranet_block_mask);
	NF_INFO("Intranet block address: %s", intra_addr_str);
	NF_INFO("Intranet block mask: %s", intra_mask_str);
	free(intra_addr_str);
	free(intra_mask_str);

	uint16_t nb_devices = rte_eth_dev_count();
	for (uint16_t dev = 0; dev < nb_devices; dev++) {
		char* dev_mac_str = nf_mac_to_str(&(config->device_macs[dev]));
		char* end_mac_str = nf_mac_to_str(&(config->endpoint_macs[dev]));

		NF_INFO("Device %" PRIu16 " own-mac: %s, end-mac: %s", dev, dev_mac_str, end_mac_str);

		free(dev_mac_str);
		free(end_mac_str);
	}

	NF_INFO("Expiration time: %" PRIu32, config->expiration_time);
	NF_INFO("Max flows: %" PRIu32, config->max_flows);

	NF_INFO("\n--- --- ------ ---\n");
}
