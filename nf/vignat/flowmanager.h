#ifndef _FLOWMANAGER_H_INCLUDED_
#define _FLOWMANAGER_H_INCLUDED_

#include "lib/flow.h"

int allocate_flowmanager(uint8_t nb_ports,
                         uint16_t starting_port, uint32_t ext_src_ip,
                         uint8_t ext_device_id,
                         uint32_t expiration_time,
                         int max_flows);

int allocate_flow(struct int_key *ik, uint32_t time, struct flow* out);
int expire_flows(uint32_t time);

int get_flow_by_int_key(struct int_key* key, uint32_t time, struct flow* flow_out);
int get_flow_by_ext_key(struct ext_key* key, uint32_t time, struct flow* flow_out);

#ifdef KLEE_VERIFICATION
struct DoubleChain** get_dchain_pp(void);
struct DoubleMap **get_dmap_pp(void);
#endif //KLEE_VERIFICATION

#endif //_FLOWMANAGER_H_INCLUDED_
