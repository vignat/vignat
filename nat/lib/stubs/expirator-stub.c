#include <klee/klee.h>
#include "lib/expirator.h"
#include "containers/double-chain-stub-control.h"

void init_expirator_stub(uint32_t exp_time) {
  klee_trace_param_i32(exp_time, "exp_time");
}
void init_expirator(uint32_t exp_time) {init_expirator_stub(exp_time);}

int expire_flows_stub(uint32_t time) {
  klee_trace_param_i32(time, "exp_time");
    int nfreed = klee_int("number_of_freed_flows");
    klee_assume(0 <= nfreed);
    if (nfreed > 0)
        dchain_stub_allocate_some();
    //Tell dchain model that we freed some indexes here
    return nfreed;
}
int expire_flows(uint32_t time) {return expire_flows_stub(time);}
