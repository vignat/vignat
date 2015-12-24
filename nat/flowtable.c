#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <rte_log.h>
#include <rte_byteorder.h>

#include "containers/map.h"
#include "flowtable.h"

#define RTE_LOGTYPE_NAT RTE_LOGTYPE_USER1

#define LOG(...) RTE_LOG(INFO, NAT, __VA_ARGS__)
#define LOG_ADD(...) printf(__VA_ARGS__)

#if MAX_FLOWS > MAP_CAPACITY
#error "The map static capacity is insufficient for this number of flows"
#endif

void log_ip(uint32_t addr) {
    LOG_ADD( "%d.%d.%d.%d", addr&0xff, (addr>>8)&0xff, (addr>>16)&0xff, (addr>>24)&0xff);
}

void log_int_key(const struct int_key *key) {
    LOG( "{int_src_port: %d(%d); dst_port: %d(%d);\n"
            " int_src_ip: ",
            key->int_src_port, rte_be_to_cpu_16(key->int_src_port),
            key->dst_port, rte_be_to_cpu_16(key->dst_port));
    log_ip(key->int_src_ip);
    LOG_ADD( "; dst_ip: ");
    log_ip(key->dst_ip);
    LOG_ADD( "\n"
            " int_device_id: %d; protocol: %d}\n",
            key->int_device_id, key->protocol);
}

void log_ext_key(const struct ext_key *key) {
    LOG( "{ext_src_port: %d(%d); dst_port: %d(%d);\n"
            " ext_src_ip: ",
            key->ext_src_port, rte_be_to_cpu_16(key->ext_src_port),
            key->dst_port, rte_be_to_cpu_16(key->dst_port));
    log_ip(key->ext_src_ip);
    LOG_ADD( "; dst_ip: ");
    log_ip(key->dst_ip);
    LOG_ADD( "\n"
            " ext_device_id: %d; protocol: %d}\n",
            key->ext_device_id, key->protocol);
}

void log_flow(const struct flow *f) {
    LOG( "{int_src_port: %d(%d); ext_src_port: %d(%d);\n"
            " dst_port: %d(%d); int_src_ip: ",
            f->int_src_port, rte_be_to_cpu_16(f->int_src_port),
            f->ext_src_port, rte_be_to_cpu_16(f->ext_src_port),
            f->dst_port, rte_be_to_cpu_16(f->dst_port));
    log_ip(f->int_src_ip);
    LOG_ADD( ";\n ext_src_ip:");
    log_ip(f->ext_src_ip);
    LOG_ADD( "; dst_ip: ");
    log_ip(f->dst_ip);
    LOG_ADD( "\n"
            " int_device_id: %d; ext_device_id: %d;\n"
            " protocol: %d}\n",
            f->int_device_id, f->ext_device_id, f->protocol);
}

struct int_key* internal_keys = NULL;
struct ext_key* external_keys = NULL;
struct flow* flows = NULL;

int* ext_bbs = NULL;
void** ext_keyps = NULL;
int* ext_khs = NULL;
int* ext_vals = NULL;

int* int_bbs = NULL;
void** int_keyps = NULL;
int* int_khs = NULL;
int* int_vals = NULL;

uint64_t num_flows = 0;

struct flow* get_flow_int(struct int_key* key) {
    LOG("look up for internal key key = \n");
    log_int_key(key);
    int index = get(int_bbs, int_keyps, int_khs, int_vals, key, sizeof(struct int_key));
    if (index == -1) {
        return NULL;
    }
    return &flows[index];
}

struct flow* get_flow_ext(struct ext_key* key) {
    LOG("look up for external key key = \n");
    log_ext_key(key);
    int index = get(ext_bbs, ext_keyps, ext_khs, ext_vals, key, sizeof(struct ext_key));
    if (index == -1) {
        return NULL;
    }
    return &flows[index];
}

static inline void fill_int_key(struct flow *f, struct int_key *k) {
    k->int_src_port = f->int_src_port;
    k->dst_port = f->dst_port;
    k->int_src_ip = f->int_src_ip;
    k->dst_ip = f->dst_ip;
    k->int_device_id = f->int_device_id;
    k->protocol = f->protocol;
}

static inline void fill_ext_key(struct flow *f, struct ext_key *k) {
    k->ext_src_port = f->ext_src_port;
    k->dst_port = f->dst_port;
    k->ext_src_ip = f->ext_src_ip;
    k->dst_ip = f->dst_ip;
    k->ext_device_id = f->ext_device_id;
    k->protocol = f->protocol;
}

//Warning: this is thread-unsafe, do not youse more than 1 lcore!
void add_flow(struct flow *f) {
    LOG("add_flow (f = \n");
    log_flow(f);
    flows[num_flows] = *f;
    fill_int_key(f, &internal_keys[num_flows]);
    fill_ext_key(f, &external_keys[num_flows]);

    assert(get_flow_ext(&external_keys[num_flows]) == NULL);
    assert(get_flow_int(&internal_keys[num_flows]) == NULL);

    int put_res = 
        put(ext_bbs, ext_keyps, ext_khs, ext_vals,
            &external_keys[num_flows], sizeof(struct int_key),
            num_flows);
    assert(put_res != -1);
    put_res =
        put(int_bbs, int_keyps, int_khs, int_vals,
            &internal_keys[num_flows], sizeof(struct ext_key),
            num_flows);
    assert(put_res != -1);

    ++num_flows;
}

int allocate_flowtables(uint8_t nb_ports) {
    //assert(internal_keys == NULL);
    //assert(external_keys == NULL);
    //assert(flows == NULL);
    //assert(int_flows == NULL);
    //assert(ext_flows == NULL);
    //assert(num_flows == 0);
    (void)nb_ports;
    if (NULL == (internal_keys = malloc(sizeof(struct int_key)*MAX_FLOWS)))
        return 0;
    if (NULL == (external_keys = malloc(sizeof(struct ext_key)*MAX_FLOWS)))
        return 0;
    if (NULL == (flows = malloc(sizeof(struct flow)*MAX_FLOWS)))
        return 0;

    // Allocate int flows map
    if (NULL == (ext_keyps = malloc(sizeof(void*)*MAP_CAPACITY)))
        return 0;
    if (NULL == (ext_khs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (ext_bbs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (ext_vals = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;

    // Allocate ext flows map
    if (NULL == (int_keyps = malloc(sizeof(void*)*MAP_CAPACITY)))
        return 0;
    if (NULL == (int_khs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (int_bbs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (int_vals = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;

    num_flows = 0;
    return 1;
}
/*
static void free_flowtables(void) {
    assert(internal_keys != NULL);
    assert(external_keys != NULL);
    assert(flows != NULL);
    assert(int_flows != NULL);
    assert(ext_flows != NULL);
    g_hash_table_destroy(int_flows); int_flows = NULL;
    g_hash_table_destroy(ext_flows); ext_flows = NULL;
    free(internal_keys); internal_keys = NULL;
    free(external_keys); external_keys = NULL;
    free(flows); flows = NULL;
    num_flows = 0;
}
*/
