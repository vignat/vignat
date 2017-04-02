#include <klee/klee.h>
#include "lib/nf_time.h"
#include "my-time-stub-control.h"

uint32_t starting_time = 0;
uint32_t last_time = 0;

uint32_t start_time(void) {
    klee_trace_ret();
    starting_time = klee_int("starting_time");
    last_time = starting_time;
    return last_time;
}

uint32_t restart_time(void) {
  starting_time = klee_int("restarting_time");
  last_time = starting_time;
  return last_time;
}

uint32_t current_time(void) {
    klee_trace_ret();
    uint32_t next_time = klee_int("next_time");
    klee_assume(last_time <= next_time);
    last_time = next_time;
    return next_time;
}

uint32_t get_start_time_internal(void) {
    return starting_time;
}
uint32_t get_start_time(void) {return get_start_time_internal();}
