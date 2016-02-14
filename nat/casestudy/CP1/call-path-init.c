#include "lib/stubs/my-time-stub-control.h"
#include "lib/my-time.h"
#include "lib/expirator.h"
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"
#include "lib/stubs/loop.h"

void to_verify()
//@ requires true;
//@ ensures true;
{
  start_time();
  init_expirator(10);
  
  int rez1 = dmap_allocate(16,16,60);
  //@ assume(rez1 == 1);
  int rez2 = dchain_allocate(1024);
  //@ assume(rez2 == 1);
  //@ close evproc_loop_invariant();
  loop_invariant_consume();
}

//rez1 == 1 && rez2 == 1 && \exists next_time: rez3 == next_time  && arg1 == rez3 ==>
// \exists number_of_freed_flows : rez4 == number_of_freed_flows
