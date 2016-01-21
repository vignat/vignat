#include "double-map-impl.h"
#include "map.h"

#if MAP_CAPACITY < DMAP_IMPL_CAPACITY
#  error "The map capacity is not sufficient for the required dmap capacity."
#endif


int dmap_impl_get(int* bbs, void** kps, int* khs, int* vals,
                  void* keyp, int key_size, int* value) {
  return get(bbs, kps, khs, vals, keyp, key_size, value);
}

int dmap_impl_put(int* bbs1, void** kps1, int* khs1, int* vals1,
                  void* keyp1, int key1_size,
                  int* bbs2, void** kps2, int* khs2, int* vals2,
                  void* keyp2, int key2_size,
                  int value) {
  return put(bbs1, kps1, khs1, vals1, keyp1, key1_size, value) &&
    put(bbs2, kps2, khs2, vals2, keyp2, key2_size, value);
}

int dmap_impl_erase(int* bbs1, void** kps1, int* khs1, void* kp1, int key1_size,
                    int* bbs2, void** kps2, int* khs2, void* kp2, int key2_size)
{
  return erase(bbs1, kps1, khs1, kp1, key1_size) &&
    erase(bbs2, kps2, khs2, kp2, key2_size);
}
int dmap_impl_size(int* bbs) {
  return size(bbs);
}

