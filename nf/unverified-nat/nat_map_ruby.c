#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include "ruby/config.h"
#include "ruby/st.h" // Modified so that st_data_t == __uint128_t (same size as nat_flow_id)

#include "nat_flow.h"
#include "nat_map.h"


struct nat_map {
	st_table* value;
};

static nat_map_hash_fn map_hash_fn;
static nat_map_eq_fn map_eq_fn;

static st_hash_type ruby_hashcmp;

static int
ruby_comparer(st_data_t left, st_data_t right)
{
	return map_eq_fn(*reinterpret_cast<nat_flow_id*>(&left), *reinterpret_cast<nat_flow_id*>(&right));
}

static st_index_t
ruby_hasher(st_data_t value)
{
	return map_hash_fn(*reinterpret_cast<nat_flow_id*>(&value));
}


void
nat_map_set_fns(nat_map_hash_fn hash_fn, nat_map_eq_fn eq_fn)
{
	map_hash_fn = hash_fn;
	map_eq_fn = eq_fn;
}

struct nat_map*
nat_map_create(uint32_t capacity)
{
	struct nat_map* map = (nat_map*) malloc(sizeof(nat_map));

	ruby_hashcmp.compare = &ruby_comparer;
	ruby_hashcmp.hash = &ruby_hasher;
	// I checked the source, st_init_table just ignores malloc errors...
	map->value = st_init_table_with_size(&ruby_hashcmp, (st_index_t) capacity);
	return map;
}

void
nat_map_insert(struct nat_map* map, nat_flow_id key, nat_flow* value)
{
	st_insert(map->value, *reinterpret_cast<st_data_t*>(&key), *reinterpret_cast<st_data_t*>(&value));
}

void
nat_map_remove(struct nat_map* map, nat_flow_id key)
{
	// st_delete takes a pointer to the value, but we don't care
	st_data_t ignored;
	st_delete(map->value, reinterpret_cast<st_data_t*>(&key), &ignored);
}

bool
nat_map_get(struct nat_map* map, nat_flow_id key, nat_flow** value)
{
	st_data_t st_value;
	if (st_lookup(map->value, *reinterpret_cast<st_data_t*>(&key), &st_value)) {
		*value = *(reinterpret_cast<nat_flow**>(&st_value));
		return true;
	}
	return false;
}
