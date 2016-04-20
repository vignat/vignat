#include <string.h>
#include <rte_log.h>
#include <rte_byteorder.h>

#include "flow.h"

#ifdef KLEE_VERIFICATION
#define LOG(...) 
#define LOG_ADD(...)
#else //KLEE_VERIFICATION
#define RTE_LOGTYPE_NAT RTE_LOGTYPE_USER1

#define LOG(...) RTE_LOG(INFO, NAT, __VA_ARGS__)
#define LOG_ADD(...) printf(__VA_ARGS__)
#endif //KLEE_VERIFICATION

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

int int_key_eq(void* a, void* b) {
  struct int_key* k1 = a;
  struct int_key* k2 = b;
  return
    (k1->int_src_port  == k2->int_src_port) &
    (k1->dst_port      == k2->dst_port) &
    (k1->int_src_ip    == k2->int_src_ip) &
    (k1->dst_ip        == k2->dst_ip) &
    (k1->int_device_id == k2->int_device_id) &
    (k1->protocol      == k2->protocol);
}

int ext_key_eq(void* a, void* b) {
  struct ext_key* k1 = a;
  struct ext_key* k2 = b;
  return
    (k1->ext_src_port  == k2->ext_src_port) &
    (k1->dst_port      == k2->dst_port) &
    (k1->ext_src_ip    == k2->ext_src_ip) &
    (k1->dst_ip        == k2->dst_ip) &
    (k1->ext_device_id == k2->ext_device_id) &
    (k1->protocol      == k2->protocol);
}

int int_key_hash(void* key) {
  struct int_key* ik = key;
  return ik->int_src_port ^ ik->dst_port ^ ik->int_src_ip ^
         ik->dst_ip ^ ik->int_device_id ^ ik->protocol;
}

int ext_key_hash(void* key) {
  struct ext_key* ek = key;
  return ek->ext_src_port ^ ek->dst_port ^ ek->ext_src_ip ^
         ek->dst_ip ^ ek->ext_device_id ^ ek->protocol;
}

void flow_extract_keys(void* flwp, void** ikpp, void** ekpp)
{
  struct flow* fp = flwp;
  *ikpp = &fp->ik;
  *ekpp = &fp->ek;
}

void flow_pack_keys(void* flwp, void* ikp, void* ekp)
{
  (void)flwp; (void)ikp; (void)ekp;
  /* do nothing */
}


void flow_cpy(char* dst, void* src) {
  memcpy(dst, src, sizeof(struct flow));
}
