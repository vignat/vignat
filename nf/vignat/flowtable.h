#ifndef _FLOWTABLE_H_INCLUDED_
#define _FLOWTABLE_H_INCLUDED_

#include "lib/flow.h"

//Warning: this is thread-unsafe, do not use with more than 1 lcore!
int get_flow_int(struct int_key* key, int* index);
int get_flow_ext(struct ext_key* key, int* index);
void get_flow(int index, struct flow* flow_out);
void set_flow(int index, struct flow* flow);
int add_flow(struct flow *f, int index);
int remove_flow(int index);

int allocate_flowtables(uint8_t nb_ports, int max_flows);

struct DoubleMap;
struct DoubleMap* get_flow_table(void);

#ifdef KLEE_VERIFICATION
struct DoubleMap **get_dmap_pp(void);
#endif //KLEE_VERIFICATION

#endif //_FLOWTABLE_H_INCLUDED_
