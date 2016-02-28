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
  struct DoubleChain* chain;
  struct DoubleMap* map;
  uint32_t next_time, next_time_1, next_time_2, next_time_3, next_time_4;
  int number_of_freed_flows, number_of_freed_flows_1;
  uint32_t arg1;
  uint16_t user_buf036;
  uint16_t user_buf034;
  uint32_t user_buf030;
  uint32_t user_buf026;//TODO: make sure these "sub-arrays" do not intersect.
  uint8_t user_buf023;
  int queue_num_i;
  int arg2 = queue_num_i;
  uint8_t val;
  int new_index;
  //@ assume(0 <= new_index);
  //@ assume(new_index < 1024);
  //@ assume(0 <= queue_num_i);
  //@ assume(queue_num_i < 2);
  struct int_key ik1;
  struct int_key* arg3 = &ik1;
  int arg4 = -1;
  int arg5;
  uint32_t arg6;
  int arg7;
  struct flow fl1;
  struct flow fl2;
  struct flow* arg8 = &fl1;
  int arg9;
  int arg10;
  struct flow* arg11 = &fl2;
  ik1.int_src_port = user_buf034;
  ik1.dst_port = user_buf036;
  ik1.int_src_ip = user_buf026;
  ik1.dst_ip = user_buf030;
  ik1.int_device_id = val;
  ik1.protocol = user_buf023;
  //@ int_k ik1_idt = ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023);
  //@ close int_k_p(&ik1, ik1_idt);
  fl1.ik.int_src_port = user_buf034;
  fl1.ik.dst_port = user_buf036;
  fl1.ik.int_src_ip = user_buf026;
  fl1.ik.dst_ip = user_buf030;
  fl1.ik.int_device_id = val;
  fl1.ik.protocol = user_buf023; //TODO: fl1.ik.* and fl1.ek.* are not yet exported by Klee.
  int tmp1 = 2747 + new_index;
  fl1.ek.ext_src_port = (uint16_t)tmp1;
  fl1.ek.dst_port = user_buf036;
  fl1.ek.ext_src_ip = 184789184;
  fl1.ek.dst_ip = user_buf030;
  fl1.ek.ext_device_id = 1;
  fl1.ek.protocol = user_buf023;
  fl1.int_src_port = user_buf034;
  int tmp2 = 2747 + new_index;
  fl1.ext_src_port = (uint16_t)tmp2;
  fl1.dst_port = user_buf036;
  fl1.int_src_ip = user_buf026;
  fl1.ext_src_ip = 184789184;
  fl1.dst_ip = user_buf030;
  fl1.int_device_id = val;
  fl1.ext_device_id = 1;
  fl1.protocol = user_buf023;

  loop_invariant_produce(&map, &chain);
  //@ open evproc_loop_invariant(?mp, ?chp);
  uint32_t rez1 = current_time();
  //@ assume(rez1 == next_time);
  loop_enumeration_begin(queue_num_i);
  uint32_t rez2 = current_time();
  //@ assume(rez2 == next_time_1);
  int rez3 = dmap_get_a(map, arg3, &arg4);
  //@ assume(rez3 == 0);
  //@ assume(arg4 == -1);
  uint32_t rez4 = current_time();
  //@ assume(rez4 == next_time_2);
  arg5 = -1;
  int rez5 = dchain_allocate_new_index(chain, &arg5, next_time_2);
  //@ assume(rez5 == 0);
  //@ assume(arg5 == -1);
  uint32_t rez6 = current_time();
  //@ assume(rez6 == next_time_3);
  //@ assume(next_time_3 > 10);
  //@ assert(dmap_dchain_coherent(?m, ?ch));
  int rez7 = expire_items(chain, map, next_time_3 - 10);
  //@ assume(rez7 == number_of_freed_flows);
  //@ expire_preserves_coherent(m, ch, next_time_3 - 10);
  //@ assert(dmap_dchain_coherent(?m2, ?ch2));
  uint32_t rez8 = current_time();
  //@ assume(rez8 == next_time_4);
  arg7 = -1;
  int rez9 = dchain_allocate_new_index(chain, &arg7, next_time_4);
  //@ assume(rez9 == 1);
  //@ assume(arg7 == new_index);
  /*@ close int_k_p(&fl1.ik, ikc(user_buf034, user_buf036, user_buf026,
                                 user_buf030, val, user_buf023));
    @*/
  /*@ close ext_k_p(&fl1.ek, ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023));
    @*/
  /*@ close flw_p(arg8, flwc(ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                             ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023),
                             user_buf034, tmp1, user_buf036, user_buf026,
                             184789184, user_buf030, val, 1, user_buf023));
    @*/
  /*@ close flow_p(flwc(ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                        ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023),
                        user_buf034, tmp1, user_buf036, user_buf026,
                        184789184, user_buf030, val, 1, user_buf023),
                   ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                   ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023));
    @*/
  /*@ close nat_flow_p
            (ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
             ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023),
             flwc(ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                  ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023),
                  user_buf034, tmp1, user_buf036, user_buf026,
                  184789184, user_buf030, val, 1, user_buf023),
             new_index);
    @*/
  /*@ dmap_erase_all_has_trans(m, ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                               dchain_get_expired_indexes_fp(ch, next_time_3 - 10));
    @*/
  //@ dchain_next_index_not_allocated(ch2);
  /*@
    if (dmap_has_k2_fp(m2, ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023))) {
       int index = dmap_get_k2_fp(m2, ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023));
       dmap_get_k2_gives_used(m2, ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023));
       flw value = dmap_get_val_fp(m2, index);
       dmap_get_by_index_rp(m2, index);
       dmap_get_by_k2_invertible(m2, ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023));
       open nat_flow_p(_, _, value, index);

       assert(index == new_index);
       assert(true == dmap_index_used_fp(m2, new_index));
       coherent_dmap_used_dchain_allocated(m2, ch2, new_index);
       assert(true == dchain_allocated_index_fp(ch2, new_index));
       assert(false);
    }
    @*/
  /*@
    if (dmap_index_used_fp(m2, new_index)) {
       coherent_dmap_used_dchain_allocated(m2, ch2, new_index);
       assert(false);
    }
    @*/
  int rez11 = dmap_put(map, arg8, new_index);
  //@ assume(rez11 == 1);
  /*@ dmap_put_get(m2, flwc(ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                            ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023),
                            user_buf034, tmp1, user_buf036, user_buf026,
                            184789184, user_buf030, val, 1, user_buf023),
                   ikc(user_buf034, user_buf036, user_buf026, user_buf030, val, user_buf023),
                   ekc(tmp1, user_buf036, 184789184, user_buf030, 1, user_buf023),
                   new_index);
    @*/
  dmap_get_value(map, new_index, arg11);
  //TODO: assert(arg11->ik... == ...);
  //TODO: assert(arg11->ek... == ...);
  //@ open flw_p(arg11, _);
  //@ assert(arg11->int_src_port == 0);
  //@ assert(arg11->ext_src_port == 2747 + new_index);
  //@ assert(arg11->dst_port == 0);
  //@ assert(arg11->int_src_ip == user_buf026);
  //@ assert(arg11->ext_src_ip == 184789184);
  //@ assert(arg11->dst_ip == user_buf030);
  //@ assert(arg11->int_device_id == val);
  //@ assert(arg11->ext_device_id == 1);
  //@ assert(arg11->protocol == user_buf023);
  //@ assert(arg11->timestamp == next_time_4);
}
