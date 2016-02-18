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
  int arg2 = queue_num_i;
  uint8_t val;
  uint32_t dmap_allocated_index;
  //@ assume(0 <= queue_num_i);
  //@ assume(queue_num_i < 2);
  uint8_t qni8 = (uint8_t)queue_num_i;
  struct int_key ik1;
  struct int_key* arg3 = &ik1;
  int arg4 = -1;
  uint32_t arg5 = dmap_allocated_index;
  uint32_t arg7 = dmap_allocated_index;
  struct flow fl;
  struct flow *arg6 = &fl;
  ik1.int_src_port = 0;
  ik1.dst_port = 0;
  ik1.int_src_ip = user_buf026;
  ik1.dst_ip = user_buf030;
  ik1.int_device_id = val;//Generalized the symbolic indexing result.
  ik1.protocol = user_buf023;
  
  loop_invariant_produce();
  //@ open evproc_loop_invariant();
  uint32_t rez1 = current_time();
  //@ assume(rez1 == next_time);
  int rez2 = expire_flows(arg1);
  //@ assume(rez2 == number_of_freed_flows);
  loop_enumeration_begin(arg2);
  uint32_t rez3 = current_time();
  //@ assume(rez3 == next_time_1);
  int rez4 = dmap_get_a(arg3, &arg4);
  //@ assume(rez4 == 1);
  //@ assume(arg4 == dmap_allocated_index);
  dmap_get_value((int)arg5, arg6);
  //@ assume(arg6->int_src_port == dmap_value32);
  //@ assume(arg6->ext_src_port == dmap_value34);
  //@ assume(arg6->dst_port == dmap_value36);
  //@ assume(arg6->int_src_ip == dmap_value40);
  //@ assume(arg6->ext_src_ip == dmap_value44);
  //@ assume(arg6->dst_ip == dmap_value48);
  //@ assume(arg6->int_device_id == dmap_value52);
  //@ assume(arg6->ext_device_id == dmap_value53);
  //@ assume(arg6->protocol == dmap_value54);
  //@ assume(arg6->timestamp == dmap_value56);
  //@ assert dmap_dchain_coherent(?map, ?chain);
  //@ domap_gives_a_allocated(map, chain, arg3, arg7);
  int rez5 = dchain_rejuvenate_index((int)arg7);
  //@ assert(rez5 == 1);
  //@ leak dmap_dchain_coherent(_,_);
  //@ leak domap_flow_at(_,_,_);
  //@ leak double_chain_p(_,_);
  //@ leak double_map_p(_,_,_,_,_,_);
  //@ leak last_time(_);
  //@ leak integer(_,_);
}
