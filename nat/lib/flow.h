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

  predicate int_k_p(struct int_key* kp; int_k k) =
    kp->int_src_port |-> ?isp &*&
    kp->dst_port |-> ?dp &*&
    kp->int_src_ip |-> ?isip &*&
    kp->dst_ip |-> ?dip &*&
    kp->int_device_id |-> ?idid &*&
    kp->protocol |-> ?prtc &*&
    k == ikc(isp, dp, isip, dip, idid, prtc);

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

  predicate ext_k_p(struct ext_key* kp; ext_k k) =
    kp->ext_src_port |-> ?esp &*&
    kp->dst_port |-> ?dp &*&
    kp->ext_src_ip |-> ?esip &*&
    kp->dst_ip |-> ?dip &*&
    kp->ext_device_id |-> ?edid &*&
    kp->protocol |-> ?prtc &*&
    k == ekc(esp, dp, esip, dip, edid, prtc);

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
  predicate flow_p(struct flow* fp, flw f) =
    fp->int_src_port |-> flw_get_isp(f) &*&
    fp->ext_src_port |-> flw_get_esp(f) &*&
    fp->dst_port |-> flw_get_dp(f) &*&
    fp->int_src_ip |-> flw_get_isip(f) &*&
    fp->ext_src_ip |-> flw_get_esip(f) &*&
    fp->dst_ip |-> flw_get_dip(f) &*&
    fp->int_device_id |-> flw_get_idid(f) &*&
    fp->ext_device_id |-> flw_get_edid(f) &*&
    fp->protocol |-> flw_get_prtc(f);

  predicate flw_p(struct flow* fp; flw f) =
    int_k_p(&fp->ik, ?ik) &*&
    ext_k_p(&fp->ek, ?ek) &*&
    fp->int_src_port |-> ?isp &*&
    fp->ext_src_port |-> ?esp &*&
    fp->dst_port |-> ?dp &*&
    fp->int_src_ip |-> ?isip &*&
    fp->ext_src_ip |-> ?esip &*&
    fp->dst_ip |-> ?dip &*&
    fp->int_device_id |-> ?idid &*&
    fp->ext_device_id |-> ?edid &*&
    fp->protocol |-> ?prtc &*&
    ik == ikc(isp, dp, isip, dip, idid, prtc) &*&
    ek == ekc(esp, dp, esip, dip, edid, prtc) &*&
    f == flwc(ik, ek, isp, esp, dp, isip, esip, dip, idid, edid, prtc);

  fixpoint bool flow_keys_offsets_fp(struct flow* fp,
                                     struct int_key* ik,
                                     struct ext_key* ek) {
    return &(fp->ik) == ik && &(fp->ek) == ek;
  }

  fixpoint int int_hash(int_k ik) {
    switch(ik) {case ikc(x1, x2, x3, x4, x5, x6):
                     return x1^x2^x3^x4^x5^x6;}
  }

  fixpoint int ext_hash(ext_k ek) {
    switch(ek) {case ekc(x1, x2, x3, x4, x5, x6):
                      return x1^x2^x3^x4^x5^x6;}
  }
  @*/

int int_key_eq(void* a, void* b);
//@ requires int_k_p(a, ?ak) &*& int_k_p(b, ?bk);
//@ ensures int_k_p(a, ak) &*& int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
int ext_key_eq(void* a, void* b);
//@ requires ext_k_p(a, ?ak) &*& ext_k_p(b, ?bk);
//@ ensures ext_k_p(a, ak) &*& ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));

int int_key_hash(void* ik);
//@ requires int_k_p(ik, ?k);
//@ ensures int_k_p(ik, k) &*& result == int_hash(k);
int ext_key_hash(void* ek);
//@ requires ext_k_p(ek, ?k);
//@ ensures ext_k_p(ek, k) &*& result == ext_hash(k);

void flow_extract_keys(void* flwp, void** ikpp, void** ekpp);
//@ requires flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            int_k_p(ikp, ?ik) &*& ext_k_p(ekp, ?ek) &*&
            true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/

void flow_pack_keys(void* flwp, void* ikp, void* ekp);
/*@ requires flow_p(flwp, ?flw) &*& int_k_p(ikp, ?ik) &*& ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures flw_p(flwp, flw);

void flow_cpy(char* dst, void* src);
//@ requires flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures flw_p(src, f) &*& flw_p((void*)dst, f);

#endif //_FLOW_H_INCLUDED_
