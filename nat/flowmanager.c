#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include "flowtable.h"
#include "containers/double-chain.h"
#include "flowmanager.h"


uint32_t expiration_time = 0;
uint16_t starting_port = 0;
uint32_t ext_src_ip = 0;
uint8_t ext_device_id = 0;

int allocate_flowmanager(uint8_t nb_ports, uint32_t _expiration_time,
                         uint16_t _starting_port, uint32_t _ext_src_ip,
                         uint8_t _ext_device_id) {
    if (0 == allocate_flowtables(nb_ports))
        return 0;
    expiration_time = _expiration_time;
    starting_port = _starting_port;
    ext_src_ip = _ext_src_ip;
    ext_device_id = _ext_device_id;
    if (0 == dchain_allocate(MAX_FLOWS))
        return 0;
    return 1;
}

int allocate_flow(struct int_key *k, uint32_t time) {
    int index = -1;
    int alloc_rez = dchain_allocate_new_index(&index);
    if (0 == alloc_rez) return 0; //Out of resources.
    uint16_t port = starting_port + index;
    struct flow new_flow = {
        .int_src_port = k->int_src_port,
        .ext_src_port = port,
        .dst_port = k->dst_port,
        .int_src_ip = k->int_src_ip,
        .ext_src_ip = ext_src_ip,
        .dst_ip = k->dst_ip,
        .int_device_id = k->int_device_id,
        .ext_device_id = ext_device_id,
        .protocol = k->protocol,
        .timestamp = time
    };
    return add_flow(&new_flow, index);
}

int expire_flows(uint32_t time) {
    /* too early to bother about expiration */
    if (time < expiration_time) return 0;
    uint32_t expired = time - expiration_time;
    int count = 0;
    int index = -1;
    while (dchain_get_oldest_index(&index)) {
        uint32_t t = get_flow(index)->timestamp;
        if (t > expired) break;
        int rez = dchain_free_index(index);
        assert(1 == rez);
        ++count;
    }
    return count;
}

static
struct flow* get_and_rejuvenate(int index, uint32_t time) {
    struct flow* ret = get_flow(index);
    dchain_rejuvenate_index(index);
    assert(time >= ret->timestamp);
    ret->timestamp = time;
    return ret;
}

struct flow* get_flow_by_int_key(struct int_key* key, uint32_t time) {
    int index = -1;
    if (!get_flow_int(key, &index))
        return NULL;
    return get_and_rejuvenate(index, time);
}

struct flow* get_flow_by_ext_key(struct ext_key* key, uint32_t time) {
    int index = -1;
    if (!get_flow_ext(key, &index))
        return NULL;
    return get_and_rejuvenate(index, time);
}
