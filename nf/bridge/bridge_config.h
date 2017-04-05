#pragma once

#include <inttypes.h>

// TODO can't really include rte_max_ethports here but need it :/


struct bridge_config {
  // Expiration time of flows in seconds
  uint32_t expiration_time;

  // Size of the dynamic filtering table
  uint32_t dyn_capacity;
};


void bridge_config_init(struct bridge_config* config,
                        int argc, char** argv);

void bridge_config_cmdline_print_usage(void);

void bridge_print_config(struct bridge_config* config);
