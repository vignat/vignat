#pragma once

#include <inttypes.h>
#include <time.h>

struct rte_mbuf;

void nf_core_init(void);
int nf_core_process(uint8_t device, struct rte_mbuf* mbuf, time_t now);

enum nf_core_special_results {
  FLOOD_FRAME = -1
};

void nf_config_init(int argc, char** argv);
void nf_config_cmdline_print_usage(void);
void nf_print_config(void);

#ifdef KLEE_VERIFICATION
void nf_loop_iteration_begin(unsigned lcore_id,
                             uint32_t time);

void nf_add_loop_iteration_assumptions(unsigned lcore_id,
                                       uint32_t time);

void nf_loop_iteration_end(unsigned lcore_id,
                           uint32_t time);
#endif //KLEE_VERIFICATION
