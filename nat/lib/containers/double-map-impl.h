#ifndef _DOUBLE_MAP_IMPL_H_INCLUDED_
#define _DOUBLE_MAP_IMPL_H_INCLUDED_

#include "boundptr.h"

#define DMAP_IMPL_CAPACITY (1024)

int dmap_impl_get(int* bbs, void** kps, int* khs, int* vals,
                  boundptr keyp, int* value);
int dmap_impl_put(int* bbs1, void** kps1, int* khs1, int* vals1,
                  boundptr keyp1,
                  int* bbs2, void** kps2, int* khs2, int* vals2,
                  boundptr keyp2,
                  int value);
int dmap_impl_erase(int* bbs1, void** kps1, int* khs1,
                    boundptr kp1,
                    int* bbs2, void** kps2, int* khs2,
                    boundptr kp2);
int dmap_impl_size(int* bbs);

#endif // _DOUBLE_MAP_IMPL_H_INCLUDED_
