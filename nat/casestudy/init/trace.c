#include <stdint.h>
#include "lib/stubs/loop.h"
#include "lib/expirator.h"
#include "lib/my-time.h"
#include "lib/stubs/my-time-stub-control.h"
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"

void to_verify()
//@ requires true;
//@ ensures true;
{
  uint32_t arg1;
  int arg2, arg3, arg4, arg5, arg6, arg7;
  start_time();
  arg1 = 10;
  init_expirator(arg1);
  arg2 = 16;
  arg3 = 0;
  arg4 = 16;
  arg5 = 16;
  arg6 = 60;
  int rez1 = dmap_allocate(arg2, arg3, arg4, arg5, arg6);
  //@ assume(rez1 == 1);
  arg7 = 1024;
  int rez2 = dchain_allocate(arg7);
  //@ assume(rez2 == 1);
  //@ close evproc_loop_invariant();
  loop_invariant_consume();
}
