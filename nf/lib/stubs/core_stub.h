#pragma once

#include <inttypes.h>
#include <stdbool.h>

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_tcp.h>

// TODO include this file in the validator instead of copy/pasting it into its preamble

// TODO more complete stub content?
// do change the total_len in rx if this is changed!
// Need to pack this struct so that accesses via rte_pktmbuf_mtod_offset work properly
struct stub_mbuf_content {
	struct ether_hdr ether;
	struct ipv4_hdr ipv4;
	struct tcp_hdr tcp;
} __attribute__((packed));

// TODO add tracing for packet details

// mbuf tracing
struct rte_mbuf;
void stub_core_trace_rx(struct rte_mbuf** mbuf);
void stub_core_trace_tx(struct rte_mbuf* mbuf, uint16_t device);
void stub_core_trace_free(struct rte_mbuf* mbuf);


// mbuf create/free
struct rte_mempool;
bool stub_core_mbuf_create(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufp);
void stub_core_mbuf_free(struct rte_mbuf* mbuf);
