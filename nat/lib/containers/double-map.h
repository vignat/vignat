#ifndef _DOUBLE_MAP_INCLUDED_
#define _DOUBLE_MAP_INCLUDED_

#define DMAP_CAPACITY (1024)

int dmap_allocate(int key_a_size, int key_b_size, int value_size);
int dmap_get_a(void* key, int* index);
int dmap_get_b(void* key, int* index);
int dmap_put(void* key_a, void* key_b, int index);
int dmap_erase(void* key_a, void* key_b);
void* dmap_get_value(int index);
int dmap_size(void);

#endif // _DOUBLE_MAP_INCLUDED_
