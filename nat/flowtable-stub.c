#include <assert.h>
#include <klee/klee.h>
#include "flowtable.h"

#  define LOG(...) 
#  define LOG_ADD(...)

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

#define MAX_FLOWS (1024)

struct like_hash {
    struct int_key sample_int_key;
    struct ext_key sample_ext_key;
    struct flow sample_flow;
    int length;
    int initialized_sample;
    int has_next_key;
} like_hash;

struct flow* get_flow_int(struct int_key* key) {
    LOG("look up for internal key key = \n");
    log_int_key(key);
    //return g_hash_table_lookup(int_flows, key);
    if (like_hash.has_next_key) {
        klee_assert(!like_hash.initialized_sample);
        like_hash.sample_int_key = *key;

        like_hash.sample_flow.int_src_port = key->int_src_port;
        like_hash.sample_flow.dst_port = key->dst_port;
        like_hash.sample_flow.int_src_ip = key->int_src_ip;
        like_hash.sample_flow.dst_ip = key->dst_ip;
        like_hash.sample_flow.int_device_id = key->int_device_id;
        like_hash.sample_flow.protocol = key->protocol;

        like_hash.sample_ext_key.dst_port = key->dst_port;
        like_hash.sample_ext_key.dst_ip = key->dst_ip;
        like_hash.sample_ext_key.protocol = key->protocol;

	LOG("HT entry is allocated on int\n");
        like_hash.initialized_sample = 1;
        return &like_hash.sample_flow;
    } else {
        return NULL;
    }
}

struct flow* get_flow_ext(struct ext_key* key) {
    //return g_hash_table_lookup(ext_flows, key);
    if (like_hash.has_next_key) {
        klee_assert(!like_hash.initialized_sample);
        like_hash.sample_ext_key = *key;

        like_hash.sample_flow.ext_src_port = key->ext_src_port;
        like_hash.sample_flow.dst_port = key->dst_port;
        like_hash.sample_flow.ext_src_ip = key->ext_src_ip;
        like_hash.sample_flow.dst_ip = key->dst_ip;
        like_hash.sample_flow.ext_device_id = key->ext_device_id;
        like_hash.sample_flow.protocol = key->protocol;

        like_hash.sample_int_key.dst_port = key->dst_port;
        like_hash.sample_int_key.dst_ip = key->dst_ip;
        like_hash.sample_int_key.protocol = key->protocol;

	LOG("HT entry is allocated on ext\n");
        like_hash.initialized_sample = 1;
        return &like_hash.sample_flow;
    } else {
        return NULL;
    }
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
    //flows[num_flows] = *f;

    //TODO: handle overflow!!

    klee_assert(!like_hash.initialized_sample);

    like_hash.sample_flow = *f;
    fill_int_key(f, &like_hash.sample_int_key);
    fill_ext_key(f, &like_hash.sample_ext_key);

    like_hash.length++;
    like_hash.initialized_sample = 1;
    LOG("HT entry is allocated on explicit add\n");
}

int allocate_flowtables(uint8_t nb_ports) {
    klee_assert(nb_ports <= 32/*RTE_MAX_ETHPORTS*/);
    klee_make_symbolic(&like_hash, sizeof(struct like_hash), "lalala");
    klee_assume(like_hash.sample_flow.ext_src_port == like_hash.sample_ext_key.ext_src_port);
    klee_assume(like_hash.sample_flow.ext_src_ip == like_hash.sample_ext_key.ext_src_ip);
    klee_assume(like_hash.sample_flow.ext_device_id == like_hash.sample_ext_key.ext_device_id);
    klee_assume(like_hash.sample_flow.int_src_port == like_hash.sample_int_key.int_src_port);
    klee_assume(like_hash.sample_flow.int_src_ip == like_hash.sample_int_key.int_src_ip);
    klee_assume(like_hash.sample_flow.int_device_id == like_hash.sample_int_key.int_device_id);
    klee_assume(like_hash.sample_flow.int_device_id < nb_ports);
    klee_assume(like_hash.sample_flow.ext_device_id < nb_ports);
    klee_assume(like_hash.initialized_sample == 0);
    klee_assume(like_hash.length < MAX_FLOWS);
    return 1;
}
