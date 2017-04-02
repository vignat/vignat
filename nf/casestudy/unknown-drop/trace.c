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
  struct DoubleMap* arg1;
  struct DoubleChain* arg2;
  uint32_t next_time, next_time_1;
  uint32_t user_buf030;
  uint32_t user_buf026;//TODO: maker sure these "sub-arrays" do not intersect.
  uint8_t user_buf023;
  int queue_num_i;
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

  loop_invariant_produce(&arg1, &arg2);
  //@ open evproc_loop_invariant(?mp, ?chp);
  uint32_t rez1 = current_time();
  //@ assume(rez1 == next_time);
  loop_enumeration_begin(queue_num_i);
  uint32_t rez2 = current_time();
  //@ assume(rez2 == next_time_1);
  //@ close (ext_k_p(&ek1, ekc(0, 0, user_buf030, user_buf026, val, user_buf023)));
  int rez3 = dmap_get_b(arg1, arg3, &arg4);
  //@ assume(rez3 == 0);
  //@ assume(arg4 == -1);
  loop_enumeration_end();
  //@ close evproc_loop_invariant(mp, chp);
  loop_invariant_consume(&arg1, &arg2);
  //@ open ext_k_p(_,_);
}
