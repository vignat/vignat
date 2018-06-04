#include <klee/klee.h>
#include "lib/nf_time.h"
#include "time_stub_control.h"

time_t starting_time = 0;
time_t last_time = 0;

__attribute__((noinline))
time_t start_time(void) {
    klee_trace_ret();
    time_t starting_time;
    klee_make_symbolic(&starting_time, sizeof(time_t), "starting_time");
    klee_assume(starting_time >= 0);
    last_time = starting_time;
    return last_time;
}

time_t restart_time(void) {
  klee_make_symbolic(&starting_time, sizeof(time_t), "restarting_time");
  klee_assume(starting_time >= 0);
  last_time = starting_time;
  return last_time;
}

__attribute__((noinline))
time_t current_time(void) {
    klee_trace_ret();
    time_t next_time;
    klee_make_symbolic(&next_time, sizeof(time_t), "next_time");
    klee_assume(last_time <= next_time);
    last_time = next_time;
    return next_time;
}

time_t get_start_time_internal(void) {
    return starting_time;
}
time_t get_start_time(void) {return get_start_time_internal();}
