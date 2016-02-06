//@ #include "lib/predicates.gh"

typedef int entry_condition(void* key_a, void* key_b, void* value);

void dmap_set_entry_condition(entry_condition* cond);
//@ requires true;
//@ ensures true;
