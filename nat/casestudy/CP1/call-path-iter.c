#include "lib/stubs/my-time-stub-control.h"
#include "lib/my-time.h"
#include "lib/expirator.h"
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"
#include "lib/stubs/loop.h"

void to_verify(uint32_t arg1)
//@ requires true;
//@ ensures true;
{
  loop_invariant_produce();
  //@ open evproc_loop_invariant();
  uint32_t rez1 = current_time();
  int rez2 = expire_flows(arg1);
  //@ assume(rez1 == arg1);
  //@ open double_chain_p(_,_);
  //@ open double_map_p(_,_,_,_);
  //@ open last_time(_);
  ;
}

//rez1 == 1 && rez2 == 1 && \exists next_time: rez3 == next_time  && arg1 == rez3 ==>
// \exists number_of_freed_flows : rez4 == number_of_freed_flows
