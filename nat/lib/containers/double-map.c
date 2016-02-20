#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "double-map.h"
#include "double-map-impl.h"

/*
#if DMAP_IMPL_CAPACITY < capacity
#  error "The implementation dmap capacity is "
"insufficient for the declared interface capacity."
#endif
*/

int key_a_offset_g = 0,
  key_a_size_g = 0,
  key_b_offset_g = 0,
  key_b_size_g = 0,
  value_size_g = 0;
uint8_t *values = NULL;
int   *bbs_a  = NULL, *bbs_b  = NULL;
void **kps_a  = NULL;
void **kps_b  = NULL;
int   *khs_a  = NULL, *khs_b  = NULL;
int   *inds_a = NULL, *inds_b = NULL;
int n_vals = 0;
int capacity_g = 0;

map_keys_equality *eq_a_g, *eq_b_g;

static
uint32_t hash(void* keyp, int key_size)
{
  uint32_t* slice = (uint32_t*)keyp;
  int n = key_size*sizeof(uint8_t)/sizeof(uint32_t);
  uint32_t rez = 0;
  for (--n; n >= 0; --n)
    {
      rez ^= slice[n];
    }
  return rez;
}

int dmap_allocate(int key_a_size, int key_a_offset, map_keys_equality* eq_a,
                  int key_b_size, int key_b_offset, map_keys_equality* eq_b,
                  int value_size, int capacity) {
  key_a_size_g = key_a_size;
  key_a_offset_g = key_a_offset;
  key_b_size_g = key_b_size;
  key_b_offset_g = key_b_offset;
  value_size_g = value_size;
  capacity_g = capacity;

  eq_a_g = eq_a;
  eq_b_g = eq_b;

  if (NULL == (values = malloc(value_size   *capacity))) return 0;
  if (NULL == (bbs_a  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == (kps_a  = malloc(sizeof(void*)*capacity))) return 0;
  if (NULL == (khs_a  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == (inds_a = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == (bbs_b  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == (kps_b  = malloc(sizeof(void*)*capacity))) return 0;
  if (NULL == (khs_b  = malloc(sizeof(int)  *capacity))) return 0;
  if (NULL == (inds_b = malloc(sizeof(int)  *capacity))) return 0;

  dmap_impl_init(bbs_a, eq_a, bbs_b, eq_b, capacity);

  n_vals = 0;
  return 1;
}

int dmap_get_a(void* key, int* index) {
  return dmap_impl_get(bbs_a, kps_a, khs_a, inds_a, key,
                       hash(key, key_a_size_g), eq_a_g, index,
                       capacity_g);
}

int dmap_get_b(void* key, int* index) {
  return dmap_impl_get(bbs_b, kps_b, khs_b, inds_b, key,
                       hash(key, key_b_size_g), eq_b_g, index,
                       capacity_g);
}

int dmap_put(void* value, int index) {
  void* key_a = (uint8_t*)value + key_a_offset_g;
  void* key_b = (uint8_t*)value + key_b_offset_g;
  memcpy(values + index, value, value_size_g);
  int ret = dmap_impl_put(bbs_a, kps_a, khs_a, inds_a, key_a,
                          hash(key_a, key_a_size_g),
                          bbs_b, kps_b, khs_b, inds_b, key_b,
                          hash(key_b, key_b_size_g),
                          index, capacity_g);
  if (ret) ++n_vals;
  return ret;
}

int dmap_erase(void* key_a, void* key_b) {
  int ret = dmap_impl_erase(bbs_a, kps_a, khs_a, key_a,
                            eq_a_g, hash(key_a, key_a_size_g),
                            bbs_b, kps_b, khs_b, key_b,
                            eq_b_g, hash(key_b, key_b_size_g),
                            capacity_g);
  if (ret) --n_vals;
  return ret;
}

void dmap_get_value(int index, void* value_out) {
  memcpy(value_out, values + index, value_size_g);
}

void dmap_set_value(int index, void* value) {
  memcpy(values + index, value, value_size_g);
}

int dmap_size(void) {
  return n_vals;
}

