#ifndef _DOUBLE_MAP_H_INCLUDED_
#define _DOUBLE_MAP_H_INCLUDED_

#include "boundptr.h"
//@ #include "lib/predicates.gh"

#define DMAP_CAPACITY (1024)

int dmap_allocate(int key_a_size, int key_b_size, int value_size);
//@ requires 0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size;
//@ ensures result == 0 ? true : double_map_p(?map, key_a_size, key_b_size, value_size);

int dmap_get_a(boundptr key, int* index);
int dmap_get_b(boundptr key, int* index);
int dmap_put(boundptr key_a, boundptr key_b, int index);
int dmap_erase(boundptr key_a, boundptr key_b);
boundptr dmap_get_value(int index);
int dmap_size(void);

#endif // _DOUBLE_MAP_H_INCLUDED_
