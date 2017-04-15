#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

#include "lib/containers/map-impl.h"

#define SMAP_CAPACITY_UPPER_LIMIT 140000

typedef int smap_key_hash(void* k);

struct Map;

int map_allocate(map_keys_equality* keq, smap_key_hash* khash, int capacity,
                 struct Map** map_out);
int map_get(struct Map* map, void* key, int* value_out);
void map_put(struct Map* map, void* key, int value);
void map_erase(struct Map* map, void* key, void** trash);
int map_size(struct Map* map);

#endif//_MAP_H_INCLUDED_
