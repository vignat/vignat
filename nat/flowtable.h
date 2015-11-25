
#ifndef FLOWTABLE_H
#define FLOWTABLE_H

struct flow {
    uint16_t int_src_port;
    uint16_t ext_src_port;
    uint16_t dst_port;
    uint32_t int_src_ip;
    uint32_t ext_src_ip;
    uint32_t dst_ip;
    uint8_t int_device_id;
    uint8_t ext_device_id;
    uint8_t protocol;
    //TODO: timeout for removal.
};

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

void log_ip(uint32_t addr);
void log_int_key(const struct int_key *key);
void log_ext_key(const struct ext_key *key);
void log_flow(const struct flow *f);

#define MAX_FLOWS (1024)

struct flow* get_flow_int(struct int_key* key);
struct flow* get_flow_ext(struct ext_key* key);

//Warning: this is thread-unsafe, do not use with more than 1 lcore!
void add_flow(struct flow *f);

int allocate_flowtables(uint8_t nb_ports);

#endif //FLOWTABLE_H
