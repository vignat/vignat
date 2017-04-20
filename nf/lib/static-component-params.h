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

#include "lib/custom_ether_addr_def.h"

struct rte_mempool {};

struct ether_hdr {
  struct ether_addr d_addr; /**< Destination address. */
  struct ether_addr s_addr; /**< Source address. */
  uint16_t ether_type;      /**< Frame type. */
};

struct tcp_hdr {
  uint16_t src_port;  /**< TCP source port. */
  uint16_t dst_port;  /**< TCP destination port. */
  uint32_t sent_seq;  /**< TX data sequence number. */
  uint32_t recv_ack;  /**< RX data acknowledgement sequence number. */
  uint8_t  data_off;  /**< Data offset. */
  uint8_t  tcp_flags; /**< TCP flags */
  uint16_t rx_win;    /**< RX flow control window. */
  uint16_t cksum;     /**< TCP checksum. */
  uint16_t tcp_urp;   /**< TCP urgent pointer, if any. */
};

struct ipv4_hdr {
  uint8_t  version_ihl;        /**< version and header length */
  uint8_t  type_of_service;    /**< type of service */
  uint16_t total_length;        /**< length of packet */
  uint16_t packet_id;        /**< packet ID */
  uint16_t fragment_offset;    /**< fragmentation offset */
  uint8_t  time_to_live;        /**< time to live */
  uint8_t  next_proto_id;        /**< protocol ID */
  uint16_t hdr_checksum;        /**< header checksum */
  uint32_t src_addr;        /**< source address */
  uint32_t dst_addr;        /**< destination address */
};

struct user_buf {
  struct ether_hdr ether;
  struct ipv4_hdr ipv4;
  struct tcp_hdr tcp;
};

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
