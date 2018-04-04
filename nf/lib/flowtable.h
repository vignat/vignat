#ifndef _FLOWTABLE_H_INCLUDED_
#define _FLOWTABLE_H_INCLUDED_

#include "lib/flow.h"

struct DoubleMap;

//Warning: this is thread-unsafe, do not use with more than 1 lcore!
int get_flow_int(struct DoubleMap* map, struct int_key* key, int* index);
int get_flow_ext(struct DoubleMap* map, struct ext_key* key, int* index);
void get_flow(struct DoubleMap* map, int index, struct flow* flow_out);
void set_flow(struct DoubleMap* map, int index, struct flow* flow);
int add_flow(struct DoubleMap* map, struct flow *f, int index);
int remove_flow(struct DoubleMap* map, int index);

int allocate_flowtables(uint16_t nb_ports, int max_flows, struct DoubleMap** map_out);

#endif //_FLOWTABLE_H_INCLUDED_
