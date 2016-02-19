#ifndef _DOUBLE_MAP_H_INCLUDED_
#define _DOUBLE_MAP_H_INCLUDED_

//@ #include "lib/predicates.gh"

#define DMAP_CAPACITY (1024)

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

int dmap_allocate(int key_a_size, int key_a_offset,
                  int key_b_size, int key_b_offset,
                  int value_size);
//@ requires 0 < key_a_size &*& 0 < key_b_size &*& 0 < value_size;
//@ ensures result == 0 ? true : double_map_p(?map, key_a_size, key_a_offset, key_b_size, key_b_offset, value_size);

int dmap_get_a(void* key, int* index);
/*@ requires double_map_p(?map, ?key_a_size, ?a_offset, ?key_b_size, ?b_offset, ?value_size); @*/
/*@ ensures double_map_p(map, key_a_size, a_offset, key_b_size, b_offset, value_size) &*&
            result == 0 ? dmap_has_a(map, key) == false :
                          (dmap_has_a(map, key) == true &*&
                           *index |-> ?i &*& i == domap_get_a(map, key));
@*/
int dmap_get_b(void* key, int* index);
/*@ requires double_map_p(?map, ?key_a_size, ?a_offset, ?key_b_size, ?b_offset, ?value_size); @*/
/*@ ensures double_map_p(map, key_a_size, a_offset, key_b_size, b_offset, value_size) &*&
            result == 0 ? dmap_has_b(map, key) == false :
                          (dmap_has_b(map, key) == true &*&
                          *index |-> ?i &*& i == domap_get_b(map, key));
  @*/
int dmap_put(void* value, int index);
/*@ requires double_map_p(?map, ?key_a_size, ?a_offset, ?key_b_size, ?b_offset, ?value_size); @*/
/*@ ensures double_map_p(map, key_a_size, a_offset, key_b_size, b_offset, value_size) &*&
    result == 0 ? true :
                  (dmap_has_b(map, value + b_offset) == true &*&
                   dmap_has_a(map, value + a_offset) == true &*&
                   index == domap_get_a(map, value + a_offset) &*&
                   index == domap_get_b(map, value + b_offset));
  @*/
int dmap_erase(void* key_a, void* key_b);
void dmap_get_value(int index, void* value_out);
/*@ requires double_map_p(?map, ?key_a_size, ?a_offset, ?key_b_size, ?b_offset, ?value_size) &*&
             0 <= index &*& index < DMAP_CAPACITY; @*/
/*@ ensures double_map_p(map, key_a_size, a_offset, key_b_size, b_offset, value_size) &*&
            value_out != 0 &*& domap_flow_at(map, index, value_out); @*/
void dmap_set_value(int index, void* value);
//^^^ TODO: add the user-defined predicate here somehow.
int dmap_size(void);

#endif // _DOUBLE_MAP_H_INCLUDED_
