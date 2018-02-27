#pragma once

#include <inttypes.h>
#include <stdbool.h>

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_mempool.h>
#include <rte_tcp.h>


// TODO include this file in the validator instead of copy/pasting it into its preamble

// TODO more complete stub content?
// do change the total_len in rx if this is changed!
struct stub_mbuf_content {
	struct ether_hdr ether;
	struct ipv4_hdr ipv4;
	struct tcp_hdr tcp;
};

void stub_core_free(struct rte_mbuf* mbuf, bool trace);
uint16_t stub_core_rx(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufs);
uint16_t stub_core_tx(uint16_t device, struct rte_mbuf** mbufs);
