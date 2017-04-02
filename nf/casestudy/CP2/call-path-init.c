#include "lib/stubs/my-time-stub-control.h"
#include "lib/my-time.h"
#include "lib/expirator.h"
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"
#include "lib/stubs/loop.h"


int flow_consistency(void* a, void* b, void* v)
{
  return 1;
}


typedef unsigned int ui32;
typedef unsigned int ui16;
typedef unsigned int ui8;

#include "unproven.h"


void to_verify(ui32 arg1, int arg3, int arg4, int arg5, int arg6)
//@ requires true;
//@ ensures true;
{
  char arg2[32];
  start_time();
  init_expirator(10);
  dmap_set_entry_condition(flow_consistency);
  int rez1 = dmap_allocate(16,16,60);
  //@ assume(rez1 == 1);
  int rez2 = dchain_allocate(1024);
  loop_invariant_consume();
}

