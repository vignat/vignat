#include <string.h>

#include "flow.h"

int int_key_eq(void* a, void* b)
//@ requires int_k_p(a, ?ak) &*& int_k_p(b, ?bk);
//@ ensures int_k_p(a, ak) &*& int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
{
  struct int_key* k1 = a;
  struct int_key* k2 = b;
  return
    (k1->int_src_port  == k2->int_src_port) &
    (k1->dst_port      == k2->dst_port) &
    (k1->int_src_ip    == k2->int_src_ip) &
    (k1->dst_ip        == k2->dst_ip) &
    (k1->int_device_id == k2->int_device_id) &
    (k1->protocol      == k2->protocol);
}

int ext_key_eq(void* a, void* b)
//@ requires ext_k_p(a, ?ak) &*& ext_k_p(b, ?bk);
//@ ensures ext_k_p(a, ak) &*& ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
{
  struct ext_key* k1 = a;
  struct ext_key* k2 = b;
  return
    (k1->ext_src_port  == k2->ext_src_port) &
    (k1->dst_port      == k2->dst_port) &
    (k1->ext_src_ip    == k2->ext_src_ip) &
    (k1->dst_ip        == k2->dst_ip) &
    (k1->ext_device_id == k2->ext_device_id) &
    (k1->protocol      == k2->protocol);
}

int int_key_hash(void* key)
//@ requires int_k_p(ik, ?k);
//@ ensures int_k_p(ik, k) &*& result == int_hash(k);
{
  struct int_key* ik = key;
  return ik->int_src_port ^ ik->dst_port ^ ik->int_src_ip ^
         ik->dst_ip ^ ik->int_device_id ^ ik->protocol;
}

int ext_key_hash(void* key)
//@ requires ext_k_p(ek, ?k);
//@ ensures ext_k_p(ek, k) &*& result == ext_hash(k);
{
  struct ext_key* ek = key;
  return ek->ext_src_port ^ ek->dst_port ^ ek->ext_src_ip ^
         ek->dst_ip ^ ek->ext_device_id ^ ek->protocol;
}

void flow_extract_keys(void* flwp, void** ikpp, void** ekpp)
//@ requires flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures flw_p(src, f) &*& flw_p((void*)dst, f);
{
  struct flow* fp = flwp;
  *ikpp = &fp->ik;
  *ekpp = &fp->ek;
}

void flow_pack_keys(void* flwp, void* ikp, void* ekp)
//@ requires flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            int_k_p(ikp, ?ik) &*& ext_k_p(ekp, ?ek) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
{
  (void)flwp; (void)ikp; (void)ekp;
  /* do nothing */
}


void flow_cpy(char* dst, void* src)
/*@ requires flow_p(flwp, ?flw) &*& int_k_p(ikp, ?ik) &*& ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures flw_p(flwp, flw);
{
  memcpy(dst, src, sizeof(struct flow));
}
