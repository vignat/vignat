#ifndef _DOUBLE_MAP_INCLUDED_
#define _DOUBLE_MAP_INCLUDED_

//@ #include "lib/predicates.gh"

#define DMAP_CAPACITY (1024)

int dmap_allocate(int key_a_size, int key_b_size, int value_size);
//@ requires 0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size;
//@ ensures result == 0 ? true : double_map_p(?map, key_a_size, key_b_size, value_size);

int dmap_get_a(void* key, int* index);
int dmap_get_b(void* key, int* index);
int dmap_put(void* key_a, void* key_b, int index);
int dmap_erase(void* key_a, void* key_b);
void* dmap_get_value(int index);
int dmap_size(void);

#endif // _DOUBLE_MAP_INCLUDED_
