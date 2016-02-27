#ifndef _FLOW_H_INCLUDED_
#define _FLOW_H_INCLUDED_
#include <stdint.h>

struct int_key {
    uint16_t int_src_port;
    uint16_t dst_port;
    uint32_t int_src_ip;
    uint32_t dst_ip;
    uint8_t int_device_id;
    uint8_t protocol;
};

struct ext_key {
    uint16_t ext_src_port;
    uint16_t dst_port;
    uint32_t ext_src_ip;
    uint32_t dst_ip;
    uint8_t ext_device_id;
    uint8_t protocol;
};

struct flow {
    // This incapsulation simplifies memory management, but may hurt locality.
    struct int_key ik;//2.5x redundancy.
    struct ext_key ek;//Can be optimized, but we do not wont that mess.
    uint16_t int_src_port;
    uint16_t ext_src_port;
    uint16_t dst_port;
    uint32_t int_src_ip;
    uint32_t ext_src_ip;
    uint32_t dst_ip;
    uint8_t int_device_id;
    uint8_t ext_device_id;
    uint8_t protocol;
};

void log_ip(uint32_t addr);
void log_int_key(const struct int_key *key);
void log_ext_key(const struct ext_key *key);
void log_flow(const struct flow *f);

#define MAX_FLOWS (1024)


/*@
  inductive int_k = ikc(int, int, int, int, int, int);
  fixpoint int int_k_get_isp(int_k k) {
  switch(k) {case ikc(ret, x1, x2, x3, x4, x5): return ret;}
  }
  fixpoint int int_k_get_dp(int_k k) {
  switch(k) {case ikc(x10, ret, x11, x12, x13, x14): return ret;}
  }
  fixpoint int int_k_get_isip(int_k k) {
  switch(k) {case ikc(x19, x20, ret, x21, x22, x23): return ret;}
  }
  fixpoint int int_k_get_dip(int_k k) {
  switch(k) {case ikc(x28, x29, x30, ret, x31, x32): return ret;}
  }
  fixpoint int int_k_get_idid(int_k k) {
  switch(k) {case ikc(x37, x38, x39, x40, ret, x41): return ret;}
  }
  fixpoint int int_k_get_prtc(int_k k) {
  switch(k) {case ikc(x46, x47, x48, x49, x50, ret): return ret;}
  }

  predicate int_k_p(struct int_key* kp, int_k k) =
    kp->int_src_port |-> int_k_get_isp(k) &*&
    kp->dst_port |-> int_k_get_dp(k) &*&
    kp->int_src_ip |-> int_k_get_isip(k) &*&
    kp->dst_ip |-> int_k_get_dip(k) &*&
    kp->int_device_id |-> int_k_get_idid(k) &*&
    kp->protocol |-> int_k_get_prtc(k);

  
  inductive ext_k = ekc(int, int, int, int, int, int);
  fixpoint int ext_k_get_esp(ext_k k) {
  switch(k) {case ekc(ret, x1, x2, x3, x4, x5): return ret;}
  }
  fixpoint int ext_k_get_dp(ext_k k) {
  switch(k) {case ekc(x10, ret, x11, x12, x13, x14): return ret;}
  }
  fixpoint int ext_k_get_esip(ext_k k) {
  switch(k) {case ekc(x19, x20, ret, x21, x22, x23): return ret;}
  }
  fixpoint int ext_k_get_dip(ext_k k) {
  switch(k) {case ekc(x28, x29, x30, ret, x31, x32): return ret;}
  }
  fixpoint int ext_k_get_edid(ext_k k) {
  switch(k) {case ekc(x37, x38, x39, x40, ret, x41): return ret;}
  }
  fixpoint int ext_k_get_prtc(ext_k k) {
  switch(k) {case ekc(x46, x47, x48, x49, x50, ret): return ret;}
  }

  predicate ext_k_p(struct ext_key* kp, ext_k k) =
    kp->ext_src_port |-> ext_k_get_esp(k) &*&
    kp->dst_port |-> ext_k_get_dp(k) &*&
    kp->ext_src_ip |-> ext_k_get_esip(k) &*&
    kp->dst_ip |-> ext_k_get_dip(k) &*&
    kp->ext_device_id |-> ext_k_get_edid(k) &*&
    kp->protocol |-> ext_k_get_prtc(k);

  inductive flw = flwc(int_k, ext_k, int, int, int,
                       int, int, int, int, int, int);
  fixpoint int_k flw_get_ik(flw f) {
  switch(f) {case flwc(ret, x1, x2, x3, x4, x5,
                       x6, x7, x8, x9, x10): return ret;}
  }
  fixpoint ext_k flw_get_ek(flw f) {
  switch(f) {case flwc(x1, ret, x2, x3, x4, x5,
                       x6, x7, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_isp(flw f) {
  switch(f) {case flwc(x1, x2, ret, x3, x4, x5,
                       x6, x7, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_esp(flw f) {
  switch(f) {case flwc(x1, x2, x3, ret, x4, x5,
                       x6, x7, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_dp(flw f) {
  switch(f) {case flwc(x1, x4, x2, x3, ret, x5,
                       x6, x7, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_isip(flw f) {
  switch(f) {case flwc(x1, x5, x2, x3, x4, ret,
                       x6, x7, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_esip(flw f) {
  switch(f) {case flwc(x1, x6, x2, x3, x4, x5,
                       ret, x7, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_dip(flw f) {
  switch(f) {case flwc(x1, x7, x2, x3, x4, x5,
                       x6, ret, x8, x9, x10): return ret;}
  }
  fixpoint int flw_get_idid(flw f) {
  switch(f) {case flwc(x1, x8, x2, x3, x4, x5,
                       x6, x7, ret, x9, x10): return ret;}
  }
  fixpoint int flw_get_edid(flw f) {
  switch(f) {case flwc(x1, x9, x2, x3, x4, x5,
                       x6, x7, x8, ret, x10): return ret;}
  }
  fixpoint int flw_get_prtc(flw f) {
  switch(f) {case flwc(x1, x10, x2, x3, x4, x5,
                       x6, x7, x8, x9, ret): return ret;}
  }
  predicate flw_p(struct flow* fp, flw f) =
    int_k_p(&fp->ik, flw_get_ik(f)) &*&
    ext_k_p(&fp->ek, flw_get_ek(f)) &*&
    fp->int_src_port |-> flw_get_isp(f) &*&
    fp->ext_src_port |-> flw_get_esp(f) &*&
    fp->dst_port |-> flw_get_dp(f) &*&
    fp->int_src_ip |-> flw_get_isip(f) &*&
    fp->ext_src_ip |-> flw_get_esip(f) &*&
    fp->dst_ip |-> flw_get_dip(f) &*&
    fp->int_device_id |-> flw_get_idid(f) &*&
    fp->ext_device_id |-> flw_get_edid(f) &*&
    fp->protocol |-> flw_get_prtc(f);

  predicate flow_p(void* p, int_k ik, ext_k ek, int index) =
    flw_p(p,?fl) &*& flw_get_ik(fl) == ik &*& flw_get_ek(fl) == ek;
  @*/

int int_key_eq(void* a, void* b);
//@ requires int_k_p(a, ?ak) &*& int_k_p(b, ?bk);
//@ ensures int_k_p(a, ak) &*& int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
int ext_key_eq(void* a, void* b);
//@ requires ext_k_p(a, ?ak) &*& ext_k_p(b, ?bk);
//@ ensures ext_k_p(a, ak) &*& ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));

#endif //_FLOW_H_INCLUDED_
