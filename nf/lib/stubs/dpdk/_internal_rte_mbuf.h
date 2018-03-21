// used with VeriFast, cannot use #pragma
#ifndef INTERNAL_RTE_MBUF_H
#define INTERNAL_RTE_MBUF_H

#include <rte_memory.h>
#include <rte_mempool.h>

#include <lib/stubs/mbuf_content.h>

// VeriFast doesn't support unions, so this is a bit messy...
struct rte_mbuf {
//	MARKER cacheline0;
#ifdef KLEE_VERIFICATION
	// If KLEE, use the real definition
	void* buf_addr;
#else
	// HACK: Else, use the stub_mbuf_content cause the validator assumes it...
	struct stub_mbuf_content* buf_addr;
#endif
//	union {
		rte_iova_t buf_iova;
// deprecated:	rte_iova_t buf_physaddr;
//	};
//	MARKER64 rearm_data;
	uint16_t data_off;
//	union {
//		rte_atomic16_t refcnt_atomic;
		uint16_t refcnt;
//	};
	uint16_t nb_segs;
	uint16_t port;
	uint64_t ol_flags;
//	MARKER rx_descriptor_fields1;
//	union {
		uint32_t packet_type;
//		struct {
//			uint32_t l2_type:4;
//			uint32_t l3_type:4;
//			uint32_t l4_type:4;
//			uint32_t tun_type:4;
//			union {
//				uint8_t inner_esp_next_proto;
//				struct {
//					uint8_t inner_l2_type:4;
//					uint8_t inner_l3_type:4;
//				};
//			};
//			uint32_t inner_l4_type:4;
//		};
//	};
	uint32_t pkt_len;
	uint16_t data_len;
	uint16_t vlan_tci;
//	union {
		uint32_t //rss;
//		struct {
//			union {
//				struct {
//					uint16_t hash;
//					uint16_t id;
//				};
//				uint32_t lo;
//			};
//			uint32_t hi;
//		} fdir;
//		struct {
//			uint32_t lo;
//			uint32_t hi;
//		} sched;
//		uint32_t usr;
	/*}*/ hash;
	uint16_t vlan_tci_outer;
	uint16_t buf_len;
	uint64_t timestamp;
//	MARKER cacheline1 __rte_cache_min_aligned;
//	union {
//		void *userdata;
		uint64_t udata64;
//	};
	struct rte_mempool *pool;
	struct rte_mbuf *next;
//	union {
		uint64_t tx_offload;
//		struct {
//			uint64_t l2_len:7;
//			uint64_t l3_len:9;
//			uint64_t l4_len:8;
//			uint64_t tso_segsz:16;
//			uint64_t outer_l3_len:9;
//			uint64_t outer_l2_len:7;
//		};
//	};
	uint16_t priv_size;
	uint16_t timesync;
	uint32_t seqn;
};

#endif
