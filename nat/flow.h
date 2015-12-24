#ifndef _FLOW_H_INCLUDED_
#define _FLOW_H_INCLUDED_

struct int_key {
    uint16_t int_src_port;
    uint16_t dst_port;
    uint32_t int_src_ip;
    uint32_t dst_ip;
    uint8_t int_device_id;
    uint8_t protocol;
};

struct ext_key {
    uint16_t ext_src_port;
    uint16_t dst_port;
    uint32_t ext_src_ip;
    uint32_t dst_ip;
    uint8_t ext_device_id;
    uint8_t protocol;
};

struct flow {
    // This incapsulation simplifies memory management, but may hurt locality.
    struct int_key ik;//2.5x redundancy.
    struct ext_key ek;//Can be optimized, but we do not wont that mess.
    uint16_t int_src_port;
    uint16_t ext_src_port;
    uint16_t dst_port;
    uint32_t int_src_ip;
    uint32_t ext_src_ip;
    uint32_t dst_ip;
    uint8_t int_device_id;
    uint8_t ext_device_id;
    uint8_t protocol;
    uint32_t timestamp;//seconds
};

void log_ip(uint32_t addr);
void log_int_key(const struct int_key *key);
void log_ext_key(const struct ext_key *key);
void log_flow(const struct flow *f);

#define MAX_FLOWS (1024)

#endif //_FLOW_H_INCLUDED_
