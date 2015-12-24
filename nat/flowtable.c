#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <rte_log.h>

#include "containers/map.h"
#include "flowtable.h"

#if MAX_FLOWS > MAP_CAPACITY
#  error "The map static capacity is insufficient for this number of flows"
#endif

#define RTE_LOGTYPE_NAT RTE_LOGTYPE_USER1

#define LOG(...) RTE_LOG(INFO, NAT, __VA_ARGS__)
#define LOG_ADD(...) printf(__VA_ARGS__)

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

struct flow* get_flow(int index) {
    return &flows[index];
}

struct flow* get_flow_int(struct int_key* key) {
    LOG("look up for internal key key = \n");
    log_int_key(key);
    int index = -1;
    int rez = get(int_bbs, int_keyps, int_khs, int_vals, key,
                  sizeof(struct int_key), &index);
    if (rez)
        return get_flow(index);
    return NULL;
}

struct flow* get_flow_ext(struct ext_key* key) {
    LOG("look up for external key key = \n");
    log_ext_key(key);
    int index = -1;
    int rez = get(ext_bbs, ext_keyps, ext_khs, ext_vals, key,
                  sizeof(struct ext_key), &index);
    if (rez)
        return get_flow(index);
    return NULL;
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
int add_flow(struct flow *f, int index) {
    assert(0 <= index && index < MAX_FLOWS);
    LOG("add_flow (f = \n");
    log_flow(f);
    struct flow *new_flow = get_flow(index);
    *new_flow = *f;
    struct int_key* new_int_key = &new_flow->ik;
    struct ext_key* new_ext_key = &new_flow->ek;
    fill_int_key(f, new_int_key);
    fill_ext_key(f, new_ext_key);

    assert(get_flow_ext(new_ext_key) == NULL);
    assert(get_flow_int(new_int_key) == NULL);

    int put_res = 
        put(ext_bbs, ext_keyps, ext_khs, ext_vals,
            new_ext_key, sizeof(struct ext_key),
            index);
    if (0 == put_res) {
        return 0;
    }
    put_res =
        put(int_bbs, int_keyps, int_khs, int_vals,
            new_int_key, sizeof(struct int_key),
            index);
    if (0 == put_res) {
        int erase_res = 
            erase(ext_bbs, ext_keyps, ext_khs,
                  new_ext_key, sizeof(struct ext_key));
        assert(1 == erase_res);
        return 0;
    }

    ++num_flows;
    return 1;
}

int remove_flow(int index) {
    assert(0 <= index && index < MAX_FLOWS);
    struct flow* f = &flows[index];
    int erase_res =
        erase(ext_bbs, ext_keyps, ext_khs, &f->ek, sizeof(struct ext_key));
    if (0 == erase_res)
        return 0;
    erase_res = 
        erase(int_bbs, int_keyps, int_khs, &f->ik, sizeof(struct int_key));
    if (0 == erase_res)
        return 0;
    --num_flows;
    return 1;
}

int allocate_flowtables(uint8_t nb_ports) {
    //assert(internal_keys == NULL);
    //assert(external_keys == NULL);
    //assert(flows == NULL);
    //assert(int_flows == NULL);
    //assert(ext_flows == NULL);
    //assert(num_flows == 0);
    (void)nb_ports;
    //if (NULL == (internal_keys = malloc(sizeof(struct int_key)*MAX_FLOWS)))
    //    return 0;
    //if (NULL == (external_keys = malloc(sizeof(struct ext_key)*MAX_FLOWS)))
    //    return 0;
    if (NULL == (flows = malloc(sizeof(struct flow)*MAX_FLOWS)))
        return 0;

    // Allocate int flows map
    if (NULL == (ext_keyps = malloc(sizeof(void*)*MAP_CAPACITY)))
        return 0;
    if (NULL == (ext_khs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (ext_bbs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (ext_vals = malloc(sizeof(void*)*MAP_CAPACITY)))
        return 0;

    // Allocate ext flows map
    if (NULL == (int_keyps = malloc(sizeof(void*)*MAP_CAPACITY)))
        return 0;
    if (NULL == (int_khs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (int_bbs = malloc(sizeof(int)*MAP_CAPACITY)))
        return 0;
    if (NULL == (int_vals = malloc(sizeof(void*)*MAP_CAPACITY)))
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
