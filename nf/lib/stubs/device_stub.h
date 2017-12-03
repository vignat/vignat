#ifndef DEVICE_STUB_H
#define DEVICE_STUB_H
// can't use #pragma, unsupported by VeriFast

#ifdef _NO_VERIFAST_
#include <inttypes.h>
#else
#define uint16_t unsigned short
#endif

#include "rte_config.h"

struct ether_hdr;
struct ipv4_hdr;
struct tcp_hdr;
struct rte_mempool;

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

#endif
