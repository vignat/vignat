#ifndef _DOUBLE_MAP_H_INCLUDED_
#define _DOUBLE_MAP_H_INCLUDED_

#include "map.h"

//@ #include "lib/predicates.gh"

//#define DMAP_CAPACITY (1024)

/*
  This implementation expects keys to be the part of the value:
  value = {
      ...;
key_a_offset: key_a {...};
      ...;
key_b_offset: key_b {...};
      ...;
  };
 */

struct DoubleMap;
/*@
  inductive dmap<t1,t2> = dmap(list<t1>, list<t2>, int);

  predicate dmappingp<t1,t2>(dmap<t1,t2> m, struct DoubleMap* mp) = true;

  fixpoint dmap<t1,t2> dmap_put_fp(dmap<t1,t2> m, t1 k1, t2 k2, int index, void* val);

  @*/

int dmap_allocate(int key_a_size, int key_a_offset, map_keys_equality eq_a,
                  int key_b_size, int key_b_offset, map_keys_equality eq_b,
                  int value_size, int capacity,
                  struct DoubleMap** map_out);
//@ requires 0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size;
//@ ensures result == 0 ? true : double_map_p(?map);

int dmap_get_a(struct DoubleMap* map, void* key, int* index);
/*@ requires double_map_p(?map); @*/
/*@ ensures double_map_p(map) &*&
            result == 0 ? domap_has_a(map, key) == false :
                          (domap_has_a(map, key) == true &*&
                           *index |-> ?i &*& i == domap_get_a(map, key));
@*/
int dmap_get_b(struct DoubleMap* map, void* key, int* index);
/*@ requires double_map_p(?map); @*/
/*@ ensures double_map_p(map) &*&
            result == 0 ? domap_has_b(map, key) == false :
                          (domap_has_b(map, key) == true &*&
                          *index |-> ?i &*& i == domap_get_b(map, key));
  @*/
int dmap_put(struct DoubleMap* map, void* value, int index);
/*@ requires double_map_p(?map) &*&
             domap_has_a(map, value + domap_get_a_offset(map)) == false &*&
             domap_has_b(map, value + domap_get_b_offset(map)) == false;@*/
/*@ ensures
  domap_size(map) < DMAP_CAPACITY ?
   (result == 1 &*&
    double_map_p(domap_put(map, value, index))) :
   (result == 0 &*&
    double_map_p(map));
  @*/
int dmap_erase(struct DoubleMap* map, void* key_a, void* key_b);
void dmap_get_value(struct DoubleMap* map, int index, void* value_out);
/*@ requires double_map_p(?map) &*&
             0 <= index &*& index < DMAP_CAPACITY; @*/
/*@ ensures double_map_p(map) &*&
            value_out != 0 &*& domap_flow_at(map, index, value_out); @*/
void dmap_set_value(struct DoubleMap* map, int index, void* value);
//^^^ TODO: add the user-defined predicate here somehow.
int dmap_size(struct DoubleMap* map);

/*@
  lemma void domap_get_put(void* map, void* value, int index);
  requires domap_size(map) < DMAP_CAPACITY;
  ensures domap_get_a(domap_put(map, value, index), value + domap_get_a_offset(map)) == index &*&
          domap_has_a(domap_put(map, value, index), value + domap_get_a_offset(map)) == true &*&
          domap_get_b(domap_put(map, value, index), value + domap_get_b_offset(map)) == index &*&
          domap_has_b(domap_put(map, value, index), value + domap_get_b_offset(map)) == true &*&
          domap_value_at(domap_put(map, value, index), index, value);
  @*/
#endif // _DOUBLE_MAP_H_INCLUDED_
