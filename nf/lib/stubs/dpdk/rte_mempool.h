// used with VeriFast, can't use #pragma
#ifndef RTE_MEMPOOL_H
#define RTE_MEMPOOL_H

#include <stdint.h>

#define RTE_MEMZONE_NAMESIZE 32


struct rte_mempool {
	char name[RTE_MEMZONE_NAMESIZE];
//	union {
//		void *pool_data;
		uint64_t pool_id;
//	};
	void *pool_config;
//	const struct rte_memzone *mz;
	unsigned int flags;
	int socket_id;
	uint32_t size;
	uint32_t cache_size;
	uint32_t elt_size;
	uint32_t header_size;
	uint32_t trailer_size;
	unsigned private_data_size;
	int32_t ops_index;
//	struct rte_mempool_cache *local_cache;
	uint32_t populated_size;
//	struct rte_mempool_objhdr_list elt_list;
	uint32_t nb_mem_chunks;
//	struct rte_mempool_memhdr_list mem_list;
};

#endif
