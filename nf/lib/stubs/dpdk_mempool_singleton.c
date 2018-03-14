#include <rte_mempool.h>

// HACKÃ!
// Loop havocing means that any memory that changes in a loop iteration is replaced by an unconstrained symbol.
// What would normally happen is that the ixgbe driver, when initializing, takes a bunch of mbufs from the pool;
// then when RX-ing, uses one of those mbufs, and takes another one as replacement from the pool;
// then when TX-ing or freeing, places it back in the pool.
// But this means that within an iteration, the mbuf that will be taken from the pool (during RX) and the one
// that will be put back in the pool (during TX) are not the same - so they are havoced, and an unconstrained mbuf
// pointer is obviously very bad.
// Instead, we use this silly-looking mempool container here, which only holds one item (discarding others)
// and always gives it when asked for items (without any kind of copying).
// This works... as long as only 1 mbuf is in flight at a time, i.e. RX and TX must be done with a single mbuf.

static int
singleton_alloc(struct rte_mempool *mp)
{
	// just to make sure
	if (mp->pool_data != NULL) {
		return -1;
	}

	return 0;
}

static int
singleton_enqueue(struct rte_mempool *mp, void * const *obj_table, unsigned n)
{
	if (n == 0) {
		// not supposed to happen, but OK
		return 0;
	}

	if (mp->pool_data != NULL) {
		// ignore
		return 0;
	}

	mp->pool_data = *obj_table;

	return 0;
}

static int
singleton_dequeue(struct rte_mempool *mp, void **obj_table, unsigned n)
{
	if (n == 0) {
		// not supposed to happen, but OK
		return 0;
	}

	if (mp->pool_data == NULL) {
		// Bad!
		return -1;
	}

	*obj_table = mp->pool_data;
	return 1;
}

static unsigned
singleton_get_count(const struct rte_mempool *mp)
{
	return mp->pool_data == NULL ? 0 : 1;
}

static void
singleton_free(struct rte_mempool *mp)
{
	// whatever, we're leaking memory anyway...
}

static struct rte_mempool_ops ops_singleton = {
	.name = "ring_mp_mc", // use the default name to not require changes in DPDK config
	.alloc = singleton_alloc,
	.free = singleton_free,
	.enqueue = singleton_enqueue,
	.dequeue = singleton_dequeue,
	.get_count = singleton_get_count
};

MEMPOOL_REGISTER_OPS(ops_singleton);
