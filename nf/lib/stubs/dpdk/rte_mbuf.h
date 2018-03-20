// used with VeriFast, cannot use #pragma
#ifndef RTE_MBUF_H
#define RTE_MBUF_H

#include <stdlib.h>
#include <string.h>

#include <rte_mempool.h>
#include <rte_memory.h>

#include "lib/stubs/core_stub.h"

#ifdef KLEE_VERIFICATION
#include <klee/klee.h>
#else
#define klee_assert
#endif


#define RTE_MBUF_DEFAULT_BUF_SIZE (2048 + 128)


#define rte_pktmbuf_mtod_offset(m, t, o) ((t)((char *)(m)->buf_addr + (m)->data_off + (o)))
#define rte_pktmbuf_mtod(m, t) rte_pktmbuf_mtod_offset(m, t, 0)


// HACK: We need rte_mbuf fully defined for the core_stub VeriFast contracts
//       but we can't have core_stub depend on rte_mbuf.h because rte_mbuf.h includes core_stub.h
//       so we define rte_mbuf in a special file, and we only include that one in core_mbuf when VeriFast-ing
#include <_internal_rte_mbuf.h>


static void
rte_mbuf_sanity_check(const struct rte_mbuf* m, int is_header)
{
	klee_assert(m != NULL);
	klee_assert(is_header == 1);

	// TODO checks?
}

static struct rte_mempool*
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

static struct rte_mbuf*
rte_mbuf_raw_alloc(struct rte_mempool* mp)
{
	return malloc(mp->elt_size);
}

// free is called by user code, raw_free by stubs
static void
rte_pktmbuf_free(struct rte_mbuf* m)
{
	klee_assert(m != NULL);

	stub_core_trace_free(m);
	stub_core_mbuf_free(m);
}

static void
rte_mbuf_raw_free(struct rte_mbuf* m)
{
	free(m);
}

static uint16_t
rte_pktmbuf_data_room_size(struct rte_mempool *mp)
{
	return RTE_MBUF_DEFAULT_BUF_SIZE; // see pool_create
}

static uint16_t
rte_pktmbuf_priv_size(struct rte_mempool *mp)
{
	return 0; // see pool_create
}

#endif
