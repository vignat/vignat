#include "double-map-impl.h"
#include "map.h"

/*
#if MAP_CAPACITY < DMAP_IMPL_CAPACITY
#  error "The map capacity is not sufficient for the required dmap capacity."
#endif
*/

void dmap_impl_init(int* bbs1, map_keys_equality* eq1,
                    int* bbs2, map_keys_equality* eq2,
                    int capacity) {
  map_initialize(bbs1, eq1, capacity);
  map_initialize(bbs2, eq2, capacity);
}

int dmap_impl_get(int* bbs, void** kps, int* khs, int* vals,
                  void* keyp, int hash, map_keys_equality* eq,
                  int* value, int capacity) {
  return map_get(bbs, kps, khs, vals, keyp, eq, hash, value, capacity);
}

int dmap_impl_put(int* bbs1, void** kps1, int* khs1, int* vals1,
                  void* keyp1, int hash1,
                  int* bbs2, void** kps2, int* khs2, int* vals2,
                  void* keyp2, int hash2,
                  int value, int capacity) {
  return map_put(bbs1, kps1, khs1, vals1, keyp1, hash1, value, capacity) &&
    map_put(bbs2, kps2, khs2, vals2, keyp2, hash2, value, capacity);
}

int dmap_impl_erase(int* bbs1, void** kps1, int* khs1,
                    void* kp1, map_keys_equality* eq1, int hash1,
                    int* bbs2, void** kps2, int* khs2,
                    void* kp2, map_keys_equality* eq2, int hash2,
                    int capacity)
{
  return map_erase(bbs1, kps1, khs1, kp1, eq1, hash1, capacity) &&
    map_erase(bbs2, kps2, khs2, kp2, eq2, hash2, capacity);
}
int dmap_impl_size(int* bbs, int capacity) {
  return map_size(bbs, capacity);
}

