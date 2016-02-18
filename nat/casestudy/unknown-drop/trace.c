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
  int next_time, next_time_1;
  int number_of_freed_flows;
  uint32_t arg1;
  uint32_t user_buf030;
  uint32_t user_buf026;//TODO: maker sure these "sub-arrays" do not intersect.
  uint8_t user_buf023;
  int queue_num_i;
  int arg2 = queue_num_i;
  uint8_t val;
  //@ assume(0 <= queue_num_i);
  //@ assume(queue_num_i < 2);
  uint8_t qni8 = (uint8_t)queue_num_i;
  struct ext_key ek1;
  struct ext_key* arg3 = &ek1;
  int arg4 = -1;
  ek1.ext_src_port = 0;
  ek1.dst_port = 0;
  ek1.ext_src_ip = user_buf030;
  ek1.dst_ip = user_buf026;
  ek1.ext_device_id = val;//Generalized the symbolic indexing result.
  ek1.protocol = user_buf023;
  loop_invariant_produce();
  //@ open evproc_loop_invariant();
  uint32_t rez1 = current_time();
  //@ assume(rez1 == next_time);
  int rez2 = expire_flows(arg1);
  //@ assume(rez2 == number_of_freed_flows);
  loop_enumeration_begin(arg2);
  uint32_t rez3 = current_time();
  //@ assume(rez3 == next_time_1);
  int rez4 = dmap_get_b(arg3, &arg4);
  //@ assume(rez4 == 0);
  //@ assume(arg4 == -1);
  loop_enumeration_end();
  //@ close evproc_loop_invariant();
  loop_invariant_consume();
}
