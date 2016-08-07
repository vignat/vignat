#ifndef _STATIC_COMPONENT_PARAMS_H_INCLUDE_
#define _STATIC_COMPONENT_PARAMS_H_INCLUDE_

#include "include_ignored_by_verifast.h"

#ifdef KLEE_VERIFICATION
#  include "lib/stubs/rte_stubs.h"
#else//KLEE_VERIFICATION

#ifdef _NO_VERIFAST_
#  include <sys/queue.h>
#  include <rte_common.h>
#  include <rte_vect.h>
#  include <rte_byteorder.h>
#  include <rte_log.h>
#  include <rte_memory.h>
#  include <rte_memcpy.h>
#  include <rte_memzone.h>
#  include <rte_eal.h>
#  include <rte_per_lcore.h>
#  include <rte_launch.h>
#  include <rte_atomic.h>
#  include <rte_cycles.h>
#  include <rte_prefetch.h>
#  include <rte_lcore.h>
#  include <rte_per_lcore.h>
#  include <rte_branch_prediction.h>
#  include <rte_interrupts.h>
#  include <rte_pci.h>
#  include <rte_random.h>
#  include <rte_debug.h>
#  include <rte_ether.h>
#  include <rte_ethdev.h>
#  include <rte_ring.h>
#  include <rte_mempool.h>
#  include <rte_mbuf.h>
#  include <rte_ip.h>
#  include <rte_tcp.h>
#  include <rte_udp.h>
#  include <rte_string_fns.h>
#else //_NO_VERIFAST_
struct rte_mbuf {};
#define RTE_MAX_ETHPORTS 32
#define RTE_MAX_LCORE 128
#endif //_NO_VERIFAST_
#endif

#define MAX_PKT_BURST     32

#define BATCHER_EL_TYPE struct rte_mbuf *
#define BATCHER_CAPACITY MAX_PKT_BURST

#endif//_STATIC_COMPONENT_PARAMS_H_INCLUDE_
