#pragma once

#include <inttypes.h>

#include "rte_config.h"
#include "rte_ether.h"
#include "rte_ip.h"
#include "rte_mempool.h"
#include "rte_tcp.h"


// TODO include this file in the validator instead of copy/pasting it into its preamble

// TODO more complete stub content?
// do change the total_len in rx if this is changed!
struct stub_mbuf_content {
	struct ether_hdr ether;
	struct ipv4_hdr ipv4;
	struct tcp_hdr tcp;
};

struct stub_queue {
	struct rte_mempool* mb_pool;
	uint16_t port_id;
};

struct stub_device {
	struct stub_queue rx_queues[RTE_MAX_QUEUES_PER_PORT];
	struct stub_queue tx_queues[RTE_MAX_QUEUES_PER_PORT];
};


void stub_init(void);
