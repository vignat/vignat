//@ #include "lib/predicates.gh"

typedef int entry_condition(void* key_a, void* key_b, void* value);

void dmap_set_entry_condition(entry_condition* cond);
//@ requires true;
//@ ensures true;

struct str_field_descr {
  int offset;
  int width;
  char* name;
};

void dmap_set_layout(struct str_field_descr* key_a_fields, int key_a_count,
                     struct str_field_descr* key_b_fields, int key_b_count,
                     struct str_field_descr* value_fields, int value_count);
