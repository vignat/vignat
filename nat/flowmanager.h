#ifndef _FLOWMANAGER_H_INCLUDED_
#define _FLOWMANAGER_H_INCLUDED_

#include "flow.h"

int allocate_flowmanager(uint8_t nb_ports, uint32_t expiration_time,
                         uint16_t starting_port, uint32_t ext_src_ip,
                         uint8_t ext_device_id);

int allocate_flow(struct int_key *ik, uint32_t time);
int expire_flows(uint32_t time);

struct flow* get_flow_by_int_key(struct int_key* key, uint32_t time);
struct flow* get_flow_by_ext_key(struct ext_key* key, uint32_t time);

#endif //_FLOWMANAGER_H_INCLUDED_
