#include <klee/klee.h>
#include "lib/expirator.h"
#include "containers/double-chain-stub-control.h"

void init_expirator(uint32_t exp_time) {
}

int expire_flows(uint32_t time) {
    int nfreed = klee_int("number_of_freed_flows");
    klee_assume(0 <= nfreed);
    if (nfreed > 0)
        dchain_stub_allocate_some();
    //Tell dchain model that we freed some indexes here
    return nfreed;
}
