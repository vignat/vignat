#ifndef _DOUBLE_MAP_IMPL_H_INCLUDED_
#define _DOUBLE_MAP_IMPL_H_INCLUDED_

#include "map.h"

void dmap_impl_init(int* bbs1, map_keys_equality* eq1,
                    int* bbs2, map_keys_equality* eq2,
                    int capacity);
int dmap_impl_get(int* bbs, void** kps, int* khs, int* vals,
                  void* keyp, int hash, map_keys_equality* eq,
                  int* value, int capacity);
int dmap_impl_put(int* bbs1, void** kps1, int* khs1, int* vals1,
                  void* keyp1, int hash1,
                  int* bbs2, void** kps2, int* khs2, int* vals2,
                  void* keyp2, int hash2,
                  int value, int capacity);
int dmap_impl_erase(int* bbs1, void** kps1, int* khs1,
                    void* kp1, map_keys_equality* eq1, int hash1,
                    int* bbs2, void** kps2, int* khs2,
                    void* kp2, map_keys_equality* eq2, int hash2,
                    int capacity);
int dmap_impl_size(int* bbs, int capacity);

#endif // _DOUBLE_MAP_IMPL_H_INCLUDED_
