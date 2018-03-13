#pragma once

#include <inttypes.h>

#include <rte_config.h>


static const int STUB_DRIVER_DEVICES_COUNT = 2;


struct rte_mempool;

struct stub_queue {
	uint16_t port_id;
	struct rte_mempool* mb_pool;
};

struct stub_driver {
	uint16_t port_id;
	struct stub_queue rx_queues[RTE_MAX_QUEUES_PER_PORT];
	struct stub_queue tx_queues[RTE_MAX_QUEUES_PER_PORT];
};


#ifdef VIGOR_STUB_DRIVER
void stub_driver_attach(void);
#else
static inline void stub_driver_attach(void) { }
#endif
