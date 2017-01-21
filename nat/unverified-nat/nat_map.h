#pragma once

#include <stdbool.h>

#include "nat_flow.h"


struct nat_map;

typedef uint64_t (*nat_map_hash_fn)(nat_flow_id key);
typedef bool (*nat_map_eq_fn)(nat_flow_id left, nat_flow_id right);


void
nat_map_set_fns(nat_map_hash_fn hash_fn, nat_map_eq_fn eq_fn);

struct nat_map*
nat_map_create(uint32_t capacity);

void
nat_map_insert(struct nat_map* map, nat_flow_id key, nat_flow* value);

void
nat_map_remove(struct nat_map* map, nat_flow_id key);

bool
nat_map_get(struct nat_map* map, nat_flow_id key, nat_flow** value);
