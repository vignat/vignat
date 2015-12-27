#include <klee/klee.h>
#include "my-time.h"

uint32_t last_time = 0;

uint32_t current_time(void) {
    uint32_t next_time = klee_int("next_time");
    klee_assume(last_time <= next_time);
    last_time = next_time;
    return next_time;
}
