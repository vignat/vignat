#include <klee/klee.h>

#include <rte_mbuf.h>

#include "lib/stubs/device_stub.h"


void flood(struct rte_mbuf* frame,
           uint8_t skip_device,
           uint8_t nb_devices) {
  klee_trace_ret();
  KLEE_TRACE_MBUF(frame, TD_IN);
  KLEE_TRACE_USER_BUF(frame->buf_addr);
  klee_trace_param_i32(skip_device, "skip_device");
  klee_trace_param_i32(nb_devices, "nb_devices");
  klee_forbid_access(frame->buf_addr, sizeof(struct stub_mbuf_content),
                     "pkt flooded");
  klee_forbid_access(frame,
                     sizeof(struct rte_mbuf),
                     "pkt flooded");
}
