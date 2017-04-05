#include <getopt.h>
#include <inttypes.h>

#if KLEE_VERIFICATION
#  include "stubs/rte_stubs.h"
#else
  // DPDK needs these but doesn't include them. :|
#  include <linux/limits.h>
#  include <sys/types.h>

#  include <rte_common.h>
#  include <rte_ethdev.h>
#endif

#include <cmdline_parse_etheraddr.h>
#include <cmdline_parse_ipaddr.h>

#include "lib/nf_util.h"
#include "lib/nf_log.h"
#include "bridge_config.h"


#define PARSE_ERROR(format, ...) \
    bridge_config_cmdline_print_usage(); \
    rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);

void bridge_config_init(struct bridge_config* config,
                        int argc, char** argv)
{
  unsigned nb_devices = rte_eth_dev_count();

  struct option long_options[] = {
    {"expire",    required_argument,  NULL, 't'},
    {"capacity",    required_argument,  NULL, 'c'},
    {NULL,       0,      NULL, 0  }
  };

  int opt;
  while ((opt = getopt_long(argc, argv, "t:c:", long_options, NULL)) != EOF) {
    unsigned device;
    switch (opt) {
      case 't':
        config->expiration_time = nf_util_parse_int(optarg, "exp-time", 10, '\0');
        if (config->expiration_time == 0) {
          PARSE_ERROR("Expiration time must be strictly positive.\n");
        }
        break;

      case 'f':
        config->dyn_capacity = nf_util_parse_int(optarg, "capacity", 10, '\0');
        if (config->dyn_capacity <= 0) {
          PARSE_ERROR("Flow table size must be strictly positive.\n");
        }
        break;

    default:
      PARSE_ERROR("Unknown option %c", opt);
    }
  }

  // Reset getopt
  optind = 1;
}

void bridge_config_cmdline_print_usage(void)
{
  printf("Usage:\n"
    "[DPDK EAL options] --\n"
    "\t--expire <time>: flow expiration time.\n"
    "\t--capacity <n>: dynamic mac learning table capacity.\n"
  );
}

void bridge_print_config(struct bridge_config* config)
{
  NF_INFO("\n--- BRIDGE Config ---\n");

  NF_INFO("Expiration time: %" PRIu32, config->expiration_time);
  NF_INFO("Capacity: %" PRIu16, config->dyn_capacity);

  NF_INFO("\n--- --- ------ ---\n");
}
