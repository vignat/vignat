#include "expirator.h"

void init_expirator(uint32_t exp_time) {
}

int expire_flows(uint32_t time) {
    //Tell dchain model that we freed some indexes here
    return klee_int();
}
