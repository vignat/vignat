#include "lib/stubs/my-time-stub-control.h"
#include "lib/my-time.h"
#include "lib/expirator.h"
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/containers/double-map.h"
#include "lib/containers/double-chain.h"
#include "lib/stubs/loop.h"

typedef unsigned int ui32;
typedef unsigned int ui16;
typedef unsigned int ui8;

#include "unproven.h"

void to_verify(ui32 arg1, int qi)
//@ requires true;
//@ ensures true;
{
  unsigned char user_buffer0[128] = {};
  unsigned char const_arr1[256];
  //@ assume(0 <= qi);
  //@ assume(qi < 2);
  unsigned char arg2[16];
  int arg3;
  arg2[0] = 171;
  arg2[1] = 171;
  arg2[2] = user_buffer0[23];
  arg2[3] = const_arr1[qi*64 + 64];
  arg2[4] = user_buffer0[29];
  arg2[5] = user_buffer0[28];
  arg2[6] = user_buffer0[27];
  arg2[7] = user_buffer0[26];
  arg2[8] = user_buffer0[33];
  arg2[9] = user_buffer0[32];
  arg2[10] = user_buffer0[31];
  arg2[11] = user_buffer0[30];
  arg2[12] = user_buffer0[35];
  arg2[13] = user_buffer0[34];
  arg2[14] = user_buffer0[37];
  arg2[15] = user_buffer0[36];

  loop_invariant_produce();
  //@ open evproc_loop_invariant();
  ui32 rez1 = current_time();
  int rez2 = expire_flows(arg1);
  //@ assume(rez1 == arg1);
  //loop_enumeration_begin
  ui32 rez3 = current_time();
  int rez4 = dmap_get_b(arg2, &arg3);
  //@ assume(rez4 == 1);
  void* rez5 = dmap_get_value(arg3);
  //@ leak double_chain_p(_,_);
  //@ leak double_map_p(_, _, _, _);
  //@ leak last_time(_);
  //@ leak integer(_,_);
}

//rez1 == 1 && rez2 == 1 && \exists next_time: rez3 == next_time  && arg1 == rez3 ==>
// \exists number_of_freed_flows : rez4 == number_of_freed_flows
