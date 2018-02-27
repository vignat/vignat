#pragma once

#include <inttypes.h>

#include "rte_config.h"
#include "rte_mempool.h"


struct stub_queue {
	uint16_t port_id;
	struct rte_mempool* mb_pool;
};

struct stub_driver {
	uint16_t port_id;
	struct stub_queue rx_queues[RTE_MAX_QUEUES_PER_PORT];
	struct stub_queue tx_queues[RTE_MAX_QUEUES_PER_PORT];
};


void stub_driver_attach(void);
