#pragma once

#include <inttypes.h>
#include <stdbool.h>

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_tcp.h>

// TODO include this file in the validator instead of copy/pasting it into its preamble

// TODO more complete stub content?
// do change the total_len in rx if this is changed!
struct stub_mbuf_content {
	struct ether_hdr ether;
	struct ipv4_hdr ipv4;
	struct tcp_hdr tcp;
};

// TODO add tracing for packet details

// mbuf tracing
void stub_core_trace_free(struct rte_mbuf* mbuf);
void stub_core_trace_rx(struct rte_mbuf* mbuf);
void stub_core_trace_tx(struct rte_mbuf* mbuf, uint16_t device);


// mbuf create/free, for high-level stubs
struct rte_mempool;
bool stub_core_mbuf_create(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufp);
void stub_core_mbuf_free(struct rte_mbuf* mbuf);
