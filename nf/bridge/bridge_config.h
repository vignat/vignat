#pragma once

#include <inttypes.h>

// TODO can't really include rte_max_ethports here but need it :/

#define CONFIG_FNAME_LEN 512

struct bridge_config {
  // Expiration time of flows in seconds
  uint32_t expiration_time;

  // Size of the dynamic filtering table
  uint32_t dyn_capacity;

  // The static configuration file name
  char static_config_fname[CONFIG_FNAME_LEN];
};


void bridge_config_init(struct bridge_config* config,
                        int argc, char** argv);

void bridge_config_cmdline_print_usage(void);

void bridge_print_config(struct bridge_config* config);
