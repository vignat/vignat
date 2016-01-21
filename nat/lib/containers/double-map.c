#include <stdlib.h>
#include "double-map.h"
#include "double-map-impl.h"

#if DMAP_IMPL_CAPACITY < DMAP_CAPACITY
#  error "The implementation dmap capacity is "
"insufficient for the declared interface capacity."
#endif

int key_a_size_g = 0, key_b_size_g = 0, value_size_g = 0;
void **values = NULL;
int   *bbs_a  = NULL, *bbs_b  = NULL;
void **kps_a  = NULL, *kps_b  = NULL;
int   *khs_a  = NULL, *khs_b  = NULL;
int   *inds_a = NULL, *inds_b = NULL;
int n_vals = 0;

int dmap_allocate(int key_a_size, int key_b_size, int value_size) {
  key_a_size_g = key_a_size;
  key_b_size_g = key_b_size;
  value_size_g = value_size;

  if (NULL == (values = malloc(value_size *DMAP_CAPACITY))) return 0;
  if (NULL == (bbs_a  = malloc(sizeof(int)*DMAP_CAPACITY))) return 0;
  if (NULL == (kps_a  = malloc(key_a_size *DMAP_CAPACITY))) return 0;
  if (NULL == (khs_a  = malloc(sizeof(int)*DMAP_CAPACITY))) return 0;
  if (NULL == (inds_a = malloc(sizeof(int)*DMAP_CAPACITY))) return 0;
  if (NULL == (bbs_b  = malloc(sizeof(int)*DMAP_CAPACITY))) return 0;
  if (NULL == (kps_b  = malloc(key_b_size *DMAP_CAPACITY))) return 0;
  if (NULL == (khs_b  = malloc(sizeof(int)*DMAP_CAPACITY))) return 0;
  if (NULL == (inds_b = malloc(sizeof(int)*DMAP_CAPACITY))) return 0;

  n_vals = 0;
  return 1;
}

int dmap_get_a(void* key, int* index) {
  return dmap_impl_get(bbs_a, kps_a, khs_a, inds_a, key, key_a_size_g, index);
}

int dmap_get_b(void* key, int* index) {
  return dmap_impl_get(bbs_b, kps_b, khs_b, inds_b, key, key_b_size_g, index);
}

int dmap_put(void* key_a, void* key_b, int index) {
  int ret = dmap_impl_put(bbs_a, kps_a, khs_a, inds_a, key_a, key_a_size_g,
                          bbs_b, kps_b, khs_b, inds_b, key_b, key_b_size_g,
                          index);
  if (ret) ++n_vals;
  return ret;
}

int dmap_erase(void* key_a, void* key_b) {
  int ret = dmap_impl_erase(bbs_a, kps_a, khs_a, key_a, key_a_size_g,
                            bbs_b, kps_b, khs_b, key_b, key_b_size_g);
  if (ret) --n_vals;
  return ret;
}

void* dmap_get_value(int index) {
  return values + index;
}

int dmap_size(void) {
  return n_vals;
}

