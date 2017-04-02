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
  int number_of_freed_flows;
  uint32_t arg3;
  uint8_t user_buf034;
  uint16_t user_buf036;
  uint32_t user_buf030;
  uint32_t user_buf026;//TODO: maker sure these "sub-arrays" do not intersect.
  uint8_t user_buf023;
  int queue_num_i;
  int arg4 = queue_num_i;
  uint8_t val;
  int dmap_allocated_index;
  uint16_t dmap_value16;
  //@ assume(0 <= queue_num_i);
  //@ assume(queue_num_i < 2);
  uint8_t qni8 = (uint8_t)queue_num_i;
  struct int_key ik1;
  struct int_key* arg5 = &ik1;
  int arg6 = -1;
  struct flow fl;
  struct flow *arg9 = &fl;
  ik1.int_src_port = user_buf034;
  ik1.dst_port = user_buf036;
  ik1.int_src_ip = user_buf026;
  ik1.dst_ip = user_buf030;
  ik1.int_device_id = val;//Generalized the symbolic indexing result.
  ik1.protocol = user_buf023;
  
  loop_invariant_produce(&arg1, &arg2);
  //@ open evproc_loop_invariant(?mp, ?chp);
  uint32_t rez1 = current_time();
  //@ assume(rez1 == next_time);
  //@ assume(next_time >= 10);
  uint32_t tmp = next_time;
  tmp = tmp - 10;
  loop_enumeration_begin(queue_num_i);
  uint32_t rez3 = current_time();
  //@ assume(rez3 == next_time_1);
  //@ close int_k_p(arg5, ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023));
  int rez4 = dmap_get_a(arg1, arg5, &arg6);
  if (rez4 == 1) {
    //@ assume(0 <= dmap_allocated_index);
    //@ assume(dmap_allocated_index < 1024);
    //@ assume(dmap_allocated_index + 2747 == (uint32_t)dmap_value16);
    //@ assert(dmap_dchain_coherent(?m, _));
    //@ dmap_get_k1_limits(m, ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023));
    int dump_state_here;
    // @ assert(arg6 == dmap_allocated_index);
  } else {
    //@ assert(arg6 == -1);
  }
  //@ open int_k_p(_, _);
  //@ leak last_time(_);
  //@ leak dmap_dchain_coherent(_, _);
  //@ leak dmappingp<int_k, ext_k, flw>(_, _, _, _, _, _, _);
  //@ leak double_chainp(_, _, _);
}
