#include <inttypes.h>

// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>
#include <unistd.h>

#include <rte_ethdev.h>
#include <rte_mbuf.h>

#include "../lib/nf_forward.h"
#include "../lib/nf_util.h"

#include "dmz_config.h"

struct dmz_config config;

void nf_core_init(void)
{
        if (!allocate_flowmanager(rte_eth_dev_count(),
	                          0,
                                  0,
                                  0,
                                  config.expiration_time,
                                  config.max_flows)) {
                rte_exit(EXIT_FAILURE, "Could not allocate flow manager");
        }
}

uint8_t nf_core_process(uint8_t device,
                        struct rte_mbuf* mbuf,
                        uint32_t now)
{
	return 0;
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
