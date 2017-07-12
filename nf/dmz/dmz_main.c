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
