#include "double-map-impl.h"
#include "map.h"

#if MAP_CAPACITY < DMAP_IMPL_CAPACITY
#  error "The map capacity is not sufficient for the required dmap capacity."
#endif


int dmap_impl_get(int* bbs, void** kps, int* khs, int* vals,
                  boundptr keyp, int* value) {
  return get(bbs, kps, khs, vals, keyp, value);
}

int dmap_impl_put(int* bbs1, void** kps1, int* khs1, int* vals1,
                  boundptr keyp1,
                  int* bbs2, void** kps2, int* khs2, int* vals2,
                  boundptr keyp2,
                  int value) {
  return put(bbs1, kps1, khs1, vals1, keyp1, value) &&
    put(bbs2, kps2, khs2, vals2, keyp2, value);
}

int dmap_impl_erase(int* bbs1, void** kps1, int* khs1, boundptr kp1,
                    int* bbs2, void** kps2, int* khs2, boundptr kp2)
{
  return erase(bbs1, kps1, khs1, kp1) &&
    erase(bbs2, kps2, khs2, kp2);
}
int dmap_impl_size(int* bbs) {
  return size(bbs);
}

