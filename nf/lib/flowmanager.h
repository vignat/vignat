#ifndef _FLOWMANAGER_H_INCLUDED_
#define _FLOWMANAGER_H_INCLUDED_

#include "lib/flow.h"
#include "lib/nf_time.h"

struct FlowManager;
struct FlowManager* allocate_flowmanager(uint16_t nb_ports,
                                         uint16_t starting_port,
                                         uint32_t ext_src_ip,
                                         uint16_t ext_device_id,
                                         uint32_t expiration_time,
                                         int max_flows);

int allocate_flow(struct FlowManager* manager, struct int_key *ik, time_t time, struct flow* out);
int expire_flows(struct FlowManager* manager, time_t time);

int get_flow_by_int_key(struct FlowManager* manager, struct int_key* key, time_t time, struct flow* flow_out);
int get_flow_by_ext_key(struct FlowManager* manager, struct ext_key* key, time_t time, struct flow* flow_out);

#ifdef KLEE_VERIFICATION
struct DoubleChain** get_dchain_pp(struct FlowManager* manager);
struct DoubleMap **get_dmap_pp(struct FlowManager* manager);
#endif //KLEE_VERIFICATION

#endif //_FLOWMANAGER_H_INCLUDED_
