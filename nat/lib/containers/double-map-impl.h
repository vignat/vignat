#ifndef _DOUBLE_MAP_IMPL_H_INCLUDED_
#define _DOUBLE_MAP_IMPL_H_INCLUDED_

#define DMAP_IMPL_CAPACITY (1024)

int dmap_impl_get(int* bbs, void** kps, int* khs, int* vals,
                  void* keyp, int key_size, int* value);
int dmap_impl_put(int* bbs1, void** kps1, int* khs1, int* vals1,
                  void* keyp1, int key1_size,
                  int* bbs2, void** kps2, int* khs2, int* vals2,
                  void* keyp2, int key2_size,
                  int value);
int dmap_impl_erase(int* bbs1, void** kps1, int* khs1,
                    void* kp1, int k1_size,
                    int* bbs2, void** kps2, int* khs2,
                    void* kp2, int k2_size);
int dmap_impl_size(int* bbs);

#endif // _DOUBLE_MAP_IMPL_H_INCLUDED_
