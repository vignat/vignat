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

const uint32_t DEFAULT_EXP_TIME = 300;//seconds
const uint32_t DEFAULT_CAPACITY = 128;//MAC addresses

#define PARSE_ERROR(format, ...) \
    bridge_config_cmdline_print_usage(); \
    rte_exit(EXIT_FAILURE, format, ##__VA_ARGS__);

void bridge_config_init(struct bridge_config* config,
                        int argc, char** argv)
{
  // Set the default values
  config->expiration_time = DEFAULT_EXP_TIME; //seconds
  config->dyn_capacity = DEFAULT_CAPACITY; //MAC addresses
  config->static_config_fname[0] = '\0';//no static filtering configuration

  unsigned nb_devices = rte_eth_dev_count();

  struct option long_options[] = {
    {"expire",    required_argument,  NULL, 't'},
    {"capacity",    required_argument,  NULL, 'c'},
    {"config",    required_argument,  NULL, 'f'},
    {NULL,       0,      NULL, 0  }
  };

  int opt;
  while ((opt = getopt_long(argc, argv, "t:c:f:", long_options, NULL)) != EOF) {
    unsigned device;
    switch (opt) {
    case 't':
      config->expiration_time = nf_util_parse_int(optarg, "exp-time", 10, '\0');
      if (config->expiration_time == 0) {
        PARSE_ERROR("Expiration time must be strictly positive.\n");
      }
      break;

    case 'c':
      config->dyn_capacity = nf_util_parse_int(optarg, "capacity", 10, '\0');
      if (config->dyn_capacity <= 0) {
        PARSE_ERROR("Flow table size must be strictly positive.\n");
      }
      break;

    case 'f':
      strncpy(config->static_config_fname, optarg,
              CONFIG_FNAME_LEN - 1);
      config->static_config_fname[CONFIG_FNAME_LEN - 1] = '\0';
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
         "\t--expire <time>: flow expiration time, default: %" PRIu32 ".\n"
         "\t--capacity <n>: dynamic mac learning table capacity,"
         " default: %" PRIu32 ".\n"
         "\t--config <fname>: static filtering table configuration file.\n",
         DEFAULT_EXP_TIME,
         DEFAULT_CAPACITY);
}

void bridge_print_config(struct bridge_config* config)
{
  NF_INFO("\n--- Bridge Config ---\n");

  NF_INFO("Expiration time: %" PRIu32, config->expiration_time);
  NF_INFO("Capacity: %" PRIu16, config->dyn_capacity);
  NF_INFO("Static configuration file: %s", config->static_config_fname);

  NF_INFO("\n--- ------ ------ ---\n");
}
