#include <stdio.h>

#include "lib/static-component-params.h"

#include "flow.h"

#include "lib/nf_log.h"

inline void log_ip(uint32_t addr) {
#if !ENABLE_LOG
  (void)addr;
#endif//NOLOG
  NF_DEBUG( "%d.%d.%d.%d",
            addr&0xff, (addr>>8)&0xff,
            (addr>>16)&0xff, (addr>>24)&0xff);
}

void log_int_key(const struct int_key *key) {
  NF_DEBUG( "{int_src_port: %d(%d); dst_port: %d(%d);\n"
            " int_src_ip: ",
            key->int_src_port, rte_be_to_cpu_16(key->int_src_port),
            key->dst_port, rte_be_to_cpu_16(key->dst_port));
  log_ip(key->int_src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(key->dst_ip);
  NF_DEBUG(" int_device_id: %d; protocol: %d}",
           key->int_device_id, key->protocol);
}

void log_ext_key(const struct ext_key *key) {
  NF_DEBUG( "{ext_src_port: %d(%d); dst_port: %d(%d);\n"
            " ext_src_ip: ",
            key->ext_src_port, rte_be_to_cpu_16(key->ext_src_port),
            key->dst_port, rte_be_to_cpu_16(key->dst_port));
  log_ip(key->ext_src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(key->dst_ip);
  NF_DEBUG(" ext_device_id: %d; protocol: %d}",
           key->ext_device_id, key->protocol);
}

void log_flow(const struct flow *f) {
  NF_DEBUG( "{int_src_port: %d(%d); ext_src_port: %d(%d);\n"
            " dst_port: %d(%d); int_src_ip: ",
            f->int_src_port, rte_be_to_cpu_16(f->int_src_port),
            f->ext_src_port, rte_be_to_cpu_16(f->ext_src_port),
            f->dst_port, rte_be_to_cpu_16(f->dst_port));
  log_ip(f->int_src_ip);
  NF_DEBUG( ";\n ext_src_ip:");
  log_ip(f->ext_src_ip);
  NF_DEBUG( "; dst_ip: ");
  log_ip(f->dst_ip);
  NF_DEBUG( " int_device_id: %d; ext_device_id: %d;\n"
            " protocol: %d}",
            f->int_device_id, f->ext_device_id, f->protocol);
}
