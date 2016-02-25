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
  uint32_t user_buf030;
  uint32_t user_buf026;//TODO: maker sure these "sub-arrays" do not intersect.
  uint8_t user_buf023;
  uint16_t dmap_value32;
  uint16_t dmap_value34;
  uint32_t dmap_value36;
  uint32_t dmap_value40;
  uint32_t dmap_value44;
  uint32_t dmap_value48;
  uint8_t dmap_value52;
  uint8_t dmap_value53;
  uint8_t dmap_value54;
  uint32_t dmap_value56;
  int queue_num_i;
  int arg4 = queue_num_i;
  uint8_t val;
  int dmap_allocated_index;
  //@ assume(0 <= queue_num_i);
  //@ assume(queue_num_i < 2);
  uint8_t qni8 = (uint8_t)queue_num_i;
  struct int_key ik1;
  struct int_key* arg5 = &ik1;
  int arg6 = -1;
  struct flow fl;
  struct flow *arg9 = &fl;
  ik1.int_src_port = 0;
  ik1.dst_port = 0;
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
  int rez2 = expire_items(arg2, arg1, tmp);
  //@ assume(rez2 == number_of_freed_flows);
  loop_enumeration_begin(queue_num_i);
  uint32_t rez3 = current_time();
  //@ assume(rez3 == next_time_1);
  //@ close int_k_p(arg5, ikc(0, 0, user_buf026, user_buf030, val, user_buf023));
  int rez4 = dmap_get_a(arg1, arg5, &arg6);
  //@ assume(rez4 == 1);
  //@ assume(arg6 == dmap_allocated_index);
  //@ assert dmappingp<int_k,ext_k>(?map, ?kp1, ?kp2, ?vp, ?cap, mp);
  //@ dmap_get_k1_gives_used(map, ikc(0, 0, user_buf026, user_buf030, val, user_buf023));
  dmap_get_value(arg1, dmap_allocated_index, arg9);
  //@ assume(arg9->int_src_port == dmap_value32);
  //@ assume(arg9->ext_src_port == dmap_value34);
  //@ assume(arg9->dst_port == dmap_value36);
  //@ assume(arg9->int_src_ip == dmap_value40);
  //@ assume(arg9->ext_src_ip == dmap_value44);
  //@ assume(arg9->dst_ip == dmap_value48);
  //@ assume(arg9->int_device_id == dmap_value52);
  //@ assume(arg9->ext_device_id == dmap_value53);
  //@ assume(arg9->protocol == dmap_value54);
  //@ assert dmap_dchain_coherent(map, ?chain);
  //@ dmap_get_k1_limits(map, ikc(0, 0, user_buf026, user_buf030, val, user_buf023));
  //@ coherent_dmap_returns_allocated(map, chain, ikc(0, 0, user_buf026, user_buf030, val, user_buf023));
  int rez5 = dchain_rejuvenate_index(arg2, dmap_allocated_index, next_time_1);
  //@ assert(rez5 == 1);
  //@ open int_k_p(_, _);
  //@ leak last_time(_);
  //@ leak flow_p(_, _, _);
  //@ leak dmap_dchain_coherent(_, _);
  //@ leak dmappingp<int_k, ext_k>(_, _, _, _, _, _);
  //@ leak double_chainp(_, _, _);
}
