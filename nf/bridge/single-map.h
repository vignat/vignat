#ifndef _SINGLE_MAP_H_INCLUDED_
#define _SINGLE_MAP_H_INCLUDED_

#include "lib/containers/map-impl.h"

#define SMAP_CAPACITY_UPPER_LIMIT 140000

typedef int smap_key_hash(void* k);

struct Map;

int smap_allocate(map_keys_equality* keq, smap_key_hash* khash, int capacity,
                  struct Map** map_out);
int smap_get(struct Map* map, void* key, int* value_out);
void smap_put(struct Map* map, void* key, int value);
void smap_erase(struct Map* map, void* key, void** trash);
int smap_size(struct Map* map);

#endif//_SINGLE_MAP_H_INCLUDED_
