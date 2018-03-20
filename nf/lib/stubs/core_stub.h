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
// HACK:
// - First, we use a double-pointer for trace_rx because the Validator doesn't support single-pointer out params
// - Second, we make _tx return a int (instead of letting callers just not call it) because the Validator
//   is currently written with the assumption that "sending" means "trying to send"; we'd need to fix that...
// - Third, we use an int instead of a bool because the Validator doesn't support bools
struct rte_mbuf;
void stub_core_trace_rx(struct rte_mbuf** mbuf);
uint8_t stub_core_trace_tx(struct rte_mbuf* mbuf, uint16_t device);
void stub_core_trace_free(struct rte_mbuf* mbuf);


// mbuf create/free
struct rte_mempool;
bool stub_core_mbuf_create(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufp);
void stub_core_mbuf_free(struct rte_mbuf* mbuf);
