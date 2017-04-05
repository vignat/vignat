#include <getopt.h>
#include <inttypes.h>

#if KLEE_VERIFICATION
	#include "stubs/rte_stubs.h"
#else
	// DPDK needs these but doesn't include them. :|
	#include <linux/limits.h>
	#include <sys/types.h>

	#include <rte_common.h>
	#include <rte_ethdev.h>
#endif

#include <cmdline_parse_etheraddr.h>
#include <cmdline_parse_ipaddr.h>

#include "nat_config.h"
#include "nf_util.h"
#include "nf_log.h"


#define PARSE_ERROR(format, ...) \
		nat_config_cmdline_print_usage(); \
		rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);


void nat_config_init(struct nat_config* config,
                     int argc, char** argv)
{
	unsigned nb_devices = rte_eth_dev_count();

	struct option long_options[] = {
		{"eth-dest",		required_argument,	NULL, 'm'},
		{"expire",		required_argument,	NULL, 't'},
		{"extip",		required_argument,	NULL, 'i'},
		{"lan-dev",		required_argument,	NULL, 'l'},
		{"max-flows",		required_argument,	NULL, 'f'},
		{"starting-port",	required_argument,	NULL, 's'},
		{"wan",			required_argument,	NULL, 'w'},
		{NULL, 			0,			NULL, 0  }
	};

	// Set the devices' own MACs
	for (uint8_t device = 0; device < nb_devices; device++) {
		rte_eth_macaddr_get(device, &(config->device_macs[device]));
	}

	int opt;
	while ((opt = getopt_long(argc, argv, "m:e:t:i:l:f:p:s:w:", long_options, NULL)) != EOF) {
		unsigned device;
		switch (opt) {
			case 'm':
				device = nf_util_parse_int(optarg, "eth-dest device", 10, ',');
				if (device >= nb_devices) {
					PARSE_ERROR("eth-dest: device %d >= nb_devices (%d)\n", device, nb_devices);
				}

				optarg += 2;
				if (cmdline_parse_etheraddr(NULL, optarg, &(config->endpoint_macs[device]), sizeof(int64_t)) < 0) {
					PARSE_ERROR("Invalid MAC address: %s\n", optarg);
				}
				break;

			case 't':
				config->expiration_time = nf_util_parse_int(optarg, "exp-time", 10, '\0');
				if (config->expiration_time == 0) {
					PARSE_ERROR("Expiration time must be strictly positive.\n");
				}
				break;

			case 'i':;
				struct cmdline_token_ipaddr tk;
				tk.ipaddr_data.flags = CMDLINE_IPADDR_V4;

				struct cmdline_ipaddr res;
				if (cmdline_parse_ipaddr((cmdline_parse_token_hdr_t*) &tk, optarg, &res, sizeof(res)) < 0) {
					PARSE_ERROR("Invalid external IP address: %s\n", optarg);
				}

				config->external_addr = res.addr.ipv4.s_addr;
				break;

			case 'l':
				config->lan_main_device = nf_util_parse_int(optarg, "lan-dev", 10, '\0');
				if (config->lan_main_device >= nb_devices) {
					PARSE_ERROR("Main LAN device does not exist.\n");
				}
				break;

			case 'f':
				config->max_flows = nf_util_parse_int(optarg, "max-flows", 10, '\0');
				if (config->max_flows <= 0) {
					PARSE_ERROR("Flow table size must be strictly positive.\n");
				}
				break;

			case 's':
				config->start_port = nf_util_parse_int(optarg, "start-port", 10, '\0');
				break;

			case 'w':
				config->wan_device = nf_util_parse_int(optarg, "wan-dev", 10, '\0');
				if (config->wan_device >= nb_devices) {
					PARSE_ERROR("WAN device does not exist.\n");
				}
				break;
		}
	}

	// Reset getopt
	optind = 1;
}

void nat_config_cmdline_print_usage(void)
{
	printf("Usage:\n"
		"[DPDK EAL options] --\n"
		"\t--eth-dest <device>,<mac>: MAC address of the endpoint linked to a device.\n"
		"\t--expire <time>: flow expiration time.\n"
		"\t--extip <ip>: external IP address.\n"
		"\t--lan-dev <device>: set device to be the main LAN device (for non-NAT).\n"
		"\t--max-flows <n>: flow table capacity.\n"
		"\t--starting-port <n>: start of the port range for external ports.\n"
		"\t--wan <device>: set device to be the external one.\n"
	);
}

void nat_print_config(struct nat_config* config)
{
	NF_INFO("\n--- NAT Config ---\n");

// TODO see remark in lcore_main
//	NF_INFO("Batch size: %" PRIu16, BATCH_SIZE);

	NF_INFO("Main LAN device: %" PRIu8, config->lan_main_device);
	NF_INFO("WAN device: %" PRIu8, config->wan_device);

	char* ext_ip_str = nf_ipv4_to_str(config->external_addr);
	NF_INFO("External IP: %s", ext_ip_str);
	free(ext_ip_str);

	uint8_t nb_devices = rte_eth_dev_count();
	for (uint8_t dev = 0; dev < nb_devices; dev++) {
		char* dev_mac_str = nf_mac_to_str(&(config->device_macs[dev]));
		char* end_mac_str = nf_mac_to_str(&(config->endpoint_macs[dev]));

		NF_INFO("Device %" PRIu8 " own-mac: %s, end-mac: %s",
            dev, dev_mac_str, end_mac_str);

		free(dev_mac_str);
		free(end_mac_str);
	}

	NF_INFO("Starting port: %" PRIu16, config->start_port);
	NF_INFO("Expiration time: %" PRIu32, config->expiration_time);
	NF_INFO("Max flows: %" PRIu16, config->max_flows);

	NF_INFO("\n--- --- ------ ---\n");
}
