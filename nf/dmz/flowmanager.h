#pragma once

#include "lib/flow.h"

int allocate_flowmanager(uint8_t nb_ports, uint32_t expiration_time, int max_flows);

int allocate_flow(struct int_key* ik, struct ext_key* ek, uint32_t time, struct flow* out);
int expire_flows(uint32_t time);

int get_flow_by_int_key(struct int_key* key, uint32_t time, struct flow* flow_out);
int get_flow_by_ext_key(struct ext_key* key, uint32_t time, struct flow* flow_out);

#ifdef KLEE_VERIFICATION
struct DoubleChain** get_dchain_pp(void);
struct DoubleMap** get_dmap_pp(void);
#endif //KLEE_VERIFICATION
