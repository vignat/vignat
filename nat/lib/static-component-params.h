#ifndef _STATIC_COMPONENT_PARAMS_H_INCLUDE_
#define _STATIC_COMPONENT_PARAMS_H_INCLUDE_

#include "include_ignored_by_verifast.h"
#include <stdint.h>

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

struct rte_mempool {};
struct user_buf {};

struct rte_mbuf {

  struct user_buf *buf_addr;           /**< Virtual address of segment buffer. */
  uint64_t buf_physaddr; /**< Physical address of segment buffer. */
  uint16_t buf_len;         /**< Length of segment buffer. */
  uint16_t data_off;
  uint16_t refcnt;              /**< Non-atomically accessed refcnt */
  uint8_t nb_segs;          /**< Number of segments. */
  uint8_t port;             /**< Input port. */
  uint64_t ol_flags;        /**< Offload features. */
  uint32_t packet_type; /**< L2/L3/L4 and tunnel information. */
  uint32_t pkt_len;         /**< Total pkt len: sum of all segments. */
  uint16_t data_len;        /**< Amount of data in segment buffer. */
  uint16_t vlan_tci;        /**< VLAN Tag Control Identifier (CPU order) */
  uint32_t hash;                   /**< hash information */
  uint32_t seqn; /**< Sequence number. See also rte_reorder_insert() */
  uint16_t vlan_tci_outer;  /**< Outer VLAN Tag Control Identifier (CPU order) */
  uint64_t udata64; /**< Allow 8-byte userdata on 32-bit */
  struct rte_mempool *pool; /**< Pool from which mbuf was allocated. */
  struct rte_mbuf *next;    /**< Next segment of scattered packet. */
  uint64_t tx_offload;       /**< combined for easy fetch */
  /** Size of the application private data. In case of an indirect
   * mbuf, it stores the direct mbuf private data size. */
  uint16_t priv_size;
  /** Timesync flags for use with IEEE1588. */
  uint16_t timesync;
};
#define RTE_MAX_ETHPORTS 32
#define RTE_MAX_LCORE 128
#endif //_NO_VERIFAST_
#endif

#define MAX_PKT_BURST     32

#define BATCHER_EL_TYPE struct rte_mbuf *
#define BATCHER_CAPACITY MAX_PKT_BURST

#endif//_STATIC_COMPONENT_PARAMS_H_INCLUDE_
