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

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

struct str_field_descr int_key_descrs[] = {
  {offsetof(struct int_key, int_src_port), sizeof(uint16_t), "int_src_port"},
  {offsetof(struct int_key, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct int_key, int_src_ip), sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct int_key, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct int_key, int_device_id), sizeof(uint8_t), "int_device_id"},
  {offsetof(struct int_key, protocol), sizeof(uint8_t), "protocol"},
};
struct str_field_descr ext_key_descrs[] = {
  {offsetof(struct ext_key, ext_src_port), sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct ext_key, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct ext_key, ext_src_ip), sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct ext_key, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct ext_key, ext_device_id), sizeof(uint8_t), "ext_device_id"},
  {offsetof(struct ext_key, protocol), sizeof(uint8_t), "protocol"},
};
struct nested_field_descr flow_nests[] = {
  {offsetof(struct flow, ik), offsetof(struct int_key, int_src_port),
   sizeof(uint16_t), "int_src_port"},
  {offsetof(struct flow, ik), offsetof(struct int_key, dst_port),
   sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, ik), offsetof(struct int_key, int_src_ip),
   sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct flow, ik), offsetof(struct int_key, dst_ip),
   sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, ik), offsetof(struct int_key, int_device_id),
   sizeof(uint8_t), "int_device_id"},
  {offsetof(struct flow, ik), offsetof(struct int_key, protocol),
   sizeof(uint8_t), "protocol"},

  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_src_port),
   sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, dst_port),
   sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_src_ip),
   sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, dst_ip),
   sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, ext_device_id),
   sizeof(uint8_t), "ext_device_id"},
  {offsetof(struct flow, ek), offsetof(struct ext_key, protocol),
   sizeof(uint8_t), "protocol"},
};

struct str_field_descr flow_descrs[] = {
  {offsetof(struct flow, ik), sizeof(struct int_key), "ik"},
  {offsetof(struct flow, ek), sizeof(struct ext_key), "ek"},
  {offsetof(struct flow, int_src_port), sizeof(uint16_t), "int_src_port"},
  {offsetof(struct flow, ext_src_port), sizeof(uint16_t), "ext_src_port"},
  {offsetof(struct flow, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct flow, int_src_ip), sizeof(uint32_t), "int_src_ip"},
  {offsetof(struct flow, ext_src_ip), sizeof(uint32_t), "ext_src_ip"},
  {offsetof(struct flow, dst_ip), sizeof(uint32_t), "dst_ip"},
  {offsetof(struct flow, int_device_id), sizeof(uint8_t), "int_device_id"},
  {offsetof(struct flow, ext_device_id), sizeof(uint8_t), "ext_device_id"},
  {offsetof(struct flow, protocol), sizeof(uint8_t), "protocol"},
};

int flow_consistency(void* key_a, void* key_b, int index, void* value) {
  struct int_key* int_key = key_a;
  struct ext_key* ext_key = key_b;
  struct flow* flow = value;
  return
#if 0 //Semantics - inessential for the crash-freedom.
    ( int_key->int_src_port == flow->int_src_port ) &
    ( int_key->dst_port == flow->dst_port ) &
    ( int_key->int_src_ip == flow->int_src_ip ) &
    ( int_key->dst_ip == flow->dst_ip ) &
    ( int_key->int_device_id == flow->int_device_id ) &
    ( int_key->protocol == flow->protocol ) &

    ( int_key->int_src_port == flow->ik.int_src_port ) &
    ( int_key->dst_port == flow->ik.dst_port ) &
    ( int_key->int_src_ip == flow->ik.int_src_ip ) &
    ( int_key->dst_ip == flow->ik.dst_ip ) &
    ( int_key->int_device_id == flow->ik.int_device_id ) &
    ( int_key->protocol == flow->ik.protocol ) &

    //(0 == memcmp(int_key, &flow->ik, sizeof(struct int_key))) &
    ( ext_key->ext_src_port == flow->ext_src_port ) &
    ( ext_key->dst_port == flow->dst_port ) &
    ( ext_key->ext_src_ip == flow->ext_src_ip ) &
    ( ext_key->dst_ip == flow->dst_ip ) &
    ( ext_key->ext_device_id == flow->ext_device_id ) &
    ( ext_key->protocol == flow->protocol ) &

    ( ext_key->ext_src_port == flow->ek.ext_src_port ) &
    ( ext_key->dst_port == flow->ek.dst_port ) &
    ( ext_key->ext_src_ip == flow->ek.ext_src_ip ) &
    ( ext_key->dst_ip == flow->ek.dst_ip ) &
    ( ext_key->ext_device_id == flow->ek.ext_device_id ) &
    ( ext_key->protocol == flow->ek.protocol ) &
#endif//0 -- inessential for crash freedom part.
    ( 0 <= flow->int_device_id) &
          (flow->int_device_id < RTE_MAX_ETHPORTS) &
    ( 0 <= flow->ext_device_id) & //FIXME: Klee translates this to signed variable
          (flow->ext_device_id < RTE_MAX_ETHPORTS) &
    ( ext_key->ext_src_port == starting_port + index) &
    ( flow->ext_src_port == starting_port + index ) &
    ( flow->ek.ext_src_port == starting_port + index );
    //(0 == memcmp(ext_key, &flow->ek, sizeof(struct ext_key)));
}

#endif//KLEE_VERIFICATION

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
    struct_int_key_padding(kp) &*&
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
    struct_ext_key_padding(kp) &*&
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
    struct_flow_padding(fp) &*&
    fp->int_src_port |-> ?isp &*&
    fp->ext_src_port |-> ?esp &*&
    fp->dst_port |-> ?dp &*&
    fp->int_src_ip |-> ?isip &*&
    fp->ext_src_ip |-> ?esip &*&
    fp->dst_ip |-> ?dip &*&
    fp->int_device_id |-> ?idid &*&
    fp->ext_device_id |-> ?edid &*&
    fp->protocol |-> ?prtc &*&
    f == flwc(ikc(isp, dp, isip, dip, idid, prtc),
              ekc(esp, dp, esip, dip, edid, prtc),
              isp, esp, dp, isip, esip, dip, idid, edid, prtc);

  predicate flw_p(struct flow* fp; flw f) =
    struct_flow_padding(fp) &*&
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

  fixpoint int overflow_cast_fp(int x) { return x <= INT_MAX ? x : x - INT_MAX - 1; }

  fixpoint int int_hash(int_k ik) {
    switch(ik) {case ikc(x1, x2, x3, x4, x5, x6):
                     return overflow_cast_fp(x1^x2^x3^x4^x5^x6);}
  }

  fixpoint int ext_hash(ext_k ek) {
    switch(ek) {case ekc(x1, x2, x3, x4, x5, x6):
                      return overflow_cast_fp(x1^x2^x3^x4^x5^x6);}
  }
  @*/

/*@
  lemma void flow_to_chars(struct flow* p);
  requires flw_p(p, _);
  ensures chars((void*)p, sizeof(struct flow), _);
  @*/

int int_key_eq(void* a, void* b);
//@ requires [?f1]int_k_p(a, ?ak) &*& [?f2]int_k_p(b, ?bk);
//@ ensures [f1]int_k_p(a, ak) &*& [f2]int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
int ext_key_eq(void* a, void* b);
//@ requires [?f1]ext_k_p(a, ?ak) &*& [?f2]ext_k_p(b, ?bk);
//@ ensures [f1]ext_k_p(a, ak) &*& [f2]ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));

int int_key_hash(void* ik);
//@ requires [?f]int_k_p(ik, ?k);
//@ ensures [f]int_k_p(ik, k) &*& result == int_hash(k);
int ext_key_hash(void* ek);
//@ requires [?f]ext_k_p(ek, ?k);
//@ ensures [f]ext_k_p(ek, k) &*& result == ext_hash(k);

void flow_destroy(void* flwp);
//@ requires flw_p(flwp, ?flw);
//@ ensures chars(flwp, sizeof(struct flow), _);

void flow_extract_keys(void* flwp, void** ikpp, void** ekpp);
//@ requires [?f]flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures [f]flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
            true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/

void flow_pack_keys(void* flwp, void* ikp, void* ekp);
/*@ requires [?f]flow_p(flwp, ?flw) &*&
             [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures [f]flw_p(flwp, flw);

void flow_cpy(char* dst, void* src);
//@ requires [?fr]flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures [fr]flw_p(src, f) &*& flw_p((void*)dst, f);

#endif //_FLOW_H_INCLUDED_
