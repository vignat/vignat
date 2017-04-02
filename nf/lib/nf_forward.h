#pragma once

#include <inttypes.h>

#include "nf_config.h"

// rte_mbuf
struct rte_mbuf;


void
nf_core_init(struct nat_config* config);

// TODO make the uint32_t a time_t
uint8_t
nf_core_process(struct nat_config* config, uint8_t device, struct rte_mbuf* mbuf, uint32_t now);
