#include "lib/stubs/my-time-stub-control.h"
#include "lib/my-time.h"
#include "lib/expirator.h"
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"

int flow_consistency(void* a, void* b, void* v)
{
  return 1;
}

void to_verify(uint32_t arg1)
//@ requires true;
//@ ensures true;
{
  start_time();
  init_expirator(10);
  entry_condition* cond = flow_consistency;
  dmap_set_entry_condition(cond);
  
  int rez1 = dmap_allocate(16,16,60);
  int rez2 = dchain_allocate(1024);
  uint32_t rez3 = current_time();
  int rez4 = expire_flows(arg1);
  
  if (rez1) {
    if (rez2) {
      ;
      //@ leak double_map_p(_,_,_,_);
      //@ leak double_chain_p(_,_);
      //@ leak last_time(_);
    } else {
      ;
      //@ leak double_map_p(_,_,_,_);
      //@ leak last_time(_);
    }
  } else {
    if (rez2) {
      ;
      //@ leak double_chain_p(_,_);
      //@ leak last_time(_);
    } else {
      ;
      //@ leak last_time(_);
    }
  }
}

//rez1 == 1 && rez2 == 1 && \exists next_time: rez3 == next_time  && arg1 == rez3 ==>
// \exists number_of_freed_flows : rez4 == number_of_freed_flows
