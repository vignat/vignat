#ifndef _DOUBLE_MAP_STUB_CONTROL_H_INCLUDED_
#define _DOUBLE_MAP_STUB_CONTROL_H_INCLUDED_
//@ #include "lib/predicates.gh"

typedef int entry_condition(void* key_a, void* key_b, int index, void* value);

void dmap_set_entry_condition(entry_condition* cond);
//@ requires true;
//@ ensures true;

struct str_field_descr {
  int offset;
  int width;
  char* name;
};

struct nested_field_descr {
  int base_offset;
  int offset;
  int width;
  char *name;
};

void dmap_set_layout(struct str_field_descr* key_a_fields, int key_a_count,
                     struct str_field_descr* key_b_fields, int key_b_count,
                     struct str_field_descr* value_fields, int value_count,
                     struct nested_field_descr* value_nested_fields, int val_nests_count);

struct DoubleMap;

void dmap_reset(struct DoubleMap* map, int capacity);

#endif//_DOUBLE_MAP_STUB_CONTROL_H_INCLUDED_
