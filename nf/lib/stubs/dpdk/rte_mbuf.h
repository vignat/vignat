#pragma once

#include <stdlib.h>
#include <string.h>

#include <rte_mempool.h>
#include <rte_memory.h>

#include "lib/stubs/core_stub.h"

#include <klee/klee.h>


#define RTE_MBUF_DEFAULT_BUF_SIZE (2048 + 128)


#define rte_pktmbuf_mtod_offset(m, t, o) ((t)((char *)(m)->buf_addr + (m)->data_off + (o)))
#define rte_pktmbuf_mtod(m, t) rte_pktmbuf_mtod_offset(m, t, 0)


struct rte_mbuf {
//	MARKER cacheline0;
	void *buf_addr;
	union {
		rte_iova_t buf_iova;
// deprecated:	rte_iova_t buf_physaddr;
	};
//	MARKER64 rearm_data;
	uint16_t data_off;
	union {
//		rte_atomic16_t refcnt_atomic;
		uint16_t refcnt;
	};
	uint16_t nb_segs;
	uint16_t port;
	uint64_t ol_flags;
//	MARKER rx_descriptor_fields1;
	union {
		uint32_t packet_type;
		struct {
			uint32_t l2_type:4;
			uint32_t l3_type:4;
			uint32_t l4_type:4;
			uint32_t tun_type:4;
			union {
				uint8_t inner_esp_next_proto;
				struct {
					uint8_t inner_l2_type:4;
					uint8_t inner_l3_type:4;
				};
			};
			uint32_t inner_l4_type:4;
		};
	};
	uint32_t pkt_len;
	uint16_t data_len;
	uint16_t vlan_tci;
	union {
		uint32_t rss;
		struct {
			union {
				struct {
					uint16_t hash;
					uint16_t id;
				};
				uint32_t lo;
			};
			uint32_t hi;
		} fdir;
		struct {
			uint32_t lo;
			uint32_t hi;
		} sched;
		uint32_t usr;
	} hash;
	uint16_t vlan_tci_outer;
	uint16_t buf_len;
	uint64_t timestamp;
//	MARKER cacheline1 __rte_cache_min_aligned;
	union {
		void *userdata;
		uint64_t udata64;
	};
	struct rte_mempool *pool;
	struct rte_mbuf *next;
	union {
		uint64_t tx_offload;
		struct {
			uint64_t l2_len:7;
			uint64_t l3_len:9;
			uint64_t l4_len:8;
			uint64_t tso_segsz:16;
			uint64_t outer_l3_len:9;
			uint64_t outer_l2_len:7;
		};
	};
	uint16_t priv_size;
	uint16_t timesync;
	uint32_t seqn;
};


static inline void
rte_mbuf_sanity_check(const struct rte_mbuf* m, int is_header)
{
	klee_assert(m != NULL);
	klee_assert(is_header == 1);

	// TODO checks?
}

static inline struct rte_mempool*
rte_pktmbuf_pool_create(const char *name, unsigned n, unsigned cache_size,
			uint16_t priv_size, uint16_t data_room_size, int socket_id)
{
	klee_assert(name != NULL);
	klee_assert(strlen(name) < RTE_MEMZONE_NAMESIZE);
	klee_assert(n > 0);
	klee_assert(cache_size >= 0);
	klee_assert(priv_size == 0); // we only support that
	klee_assert(data_room_size == RTE_MBUF_DEFAULT_BUF_SIZE); // same
	klee_assert(socket_id == 0); // same

	struct rte_mempool* pool = malloc(sizeof(struct rte_mempool));
	strcpy(pool->name, name);
	pool->elt_size = priv_size + sizeof(struct rte_mbuf) + data_room_size;
	return pool;
}

static inline struct rte_mbuf*
rte_mbuf_raw_alloc(struct rte_mempool* mp)
{
	return malloc(mp->elt_size);
}

static inline void
rte_pktmbuf_free(struct rte_mbuf* m)
{
	klee_assert(m != NULL);

	stub_core_trace_free(m);
	stub_core_mbuf_free(m);
}


static inline uint16_t
rte_pktmbuf_data_room_size(struct rte_mempool *mp)
{
	return RTE_MBUF_DEFAULT_BUF_SIZE; // see pool_create
}

static inline uint16_t
rte_pktmbuf_priv_size(struct rte_mempool *mp)
{
	return 0; // see pool_create
}
