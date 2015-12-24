#ifndef _FLOWTABLE_H_INCLUDED_
#define _FLOWTABLE_H_INCLUDED_

#include "flow.h"

//Warning: this is thread-unsafe, do not use with more than 1 lcore!
struct flow* get_flow_int(struct int_key* key);
struct flow* get_flow_ext(struct ext_key* key);
struct flow* get_flow(int index);
int add_flow(struct flow *f, int index);
int remove_flow(int index);

int allocate_flowtables(uint8_t nb_ports);


#endif //_FLOWTABLE_H_INCLUDED_
