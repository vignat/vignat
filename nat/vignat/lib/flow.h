#ifndef _FLOW_H_INCLUDED_
#define _FLOW_H_INCLUDED_
#include <stdint.h>

/**
  The "internal" key - the part of the flow ID, related to the internal network.
  Used in a hash map to identify flows for packets coming from the internal
  network.
*/
struct int_key {
  uint16_t int_src_port;
  uint16_t dst_port;
  uint32_t int_src_ip;
  uint32_t dst_ip;
  uint8_t int_device_id;
  uint8_t protocol;
};

/**
  The "external" key - the part of the flow ID, related to the external network.
  Used in a hash map to identify flows for packets coming from the external
  network.
*/
struct ext_key {
  uint16_t ext_src_port;
  uint16_t dst_port;
  uint32_t ext_src_ip;
  uint32_t dst_ip;
  uint8_t ext_device_id;
  uint8_t protocol;
};

/**
  The flow ID. A 7-tuple holding all elements necessary to identify both sides
  of a flow: the internal and the external. This structure helps NAT to
  translate between internal and external 5-tuples.
 */
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

/**
  Logging functions for the structures defined above.
*/
void log_ip(uint32_t addr);
void log_int_key(const struct int_key *key);
void log_ext_key(const struct ext_key *key);
void log_flow(const struct flow *f);

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>
#include "lib/stubs/containers/double-map-stub-control.h"
#include "lib/static-component-params.h"

//TODO: this is dirty.
extern uint16_t starting_port;

/*
  Metainformation about the structures above. Used for detailed traces in Klee
  symbolic execution engine. See dmap_set_layout in the
  double-map-stub-control.h
 */
extern struct str_field_descr int_key_descrs[6];
extern struct str_field_descr ext_key_descrs[6];
extern struct nested_field_descr flow_nests[12];
extern struct str_field_descr flow_descrs[11];

int flow_consistency(void* key_a, void* key_b,
                     int index, void* value);

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
    idid != edid &*&
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
    idid != edid &*&
    ik == ikc(isp, dp, isip, dip, idid, prtc) &*&
    ek == ekc(esp, dp, esip, dip, edid, prtc) &*&
    f == flwc(ik, ek, isp, esp, dp, isip, esip, dip, idid, edid, prtc);

  fixpoint bool flow_keys_offsets_fp(struct flow* fp,
                                     struct int_key* ik,
                                     struct ext_key* ek) {
    return &(fp->ik) == ik && &(fp->ek) == ek;
  }

  fixpoint long long _wrap(long long x) { return x % INT_MAX; }

  fixpoint int int_hash(int_k ik) {
    switch(ik) {case ikc(x1, x2, x3, x4, x5, x6):
                     return _wrap((((((x1 * 31) + x2) * 31 + x3) * 31 + x4) * 31 + x5) * 31 + x6);}
  }

  fixpoint int ext_hash(ext_k ek) {
    switch(ek) {case ekc(x1, x2, x3, x4, x5, x6):
                      return _wrap((((((x1 * 31) + x2) * 31 + x3) * 31 + x4) * 31 + x5) * 31 + x6);}
  }
  @*/

/**
  Equality comparison function for the int_key's.
  Necessary for DoubleMap, hence the generalized signature.
  @param a - pointer to the first int_key
  @param b - pointer to second int_key
  @returns 1 if *a equals *b; and 1 otherwise.
*/
int int_key_eq(void* a, void* b);
//@ requires [?f1]int_k_p(a, ?ak) &*& [?f2]int_k_p(b, ?bk);
//@ ensures [f1]int_k_p(a, ak) &*& [f2]int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));

/**
  Equality comparison function for the ext_key's.
  Necessary for DoubleMap, hence the generalized signature.
  @param a - pointer to the first ext_key
  @param b - pointer to second ext_key
  @returns 1 if *a equals *b; and 1 otherwise.
*/
int ext_key_eq(void* a, void* b);
//@ requires [?f1]ext_k_p(a, ?ak) &*& [?f2]ext_k_p(b, ?bk);
//@ ensures [f1]ext_k_p(a, ak) &*& [f2]ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));


/**
  Hash function for int_key's.
  Necessary for DoubleMap, hence the generalized signature.

  @param ik - pointer to the int_key.
  @returns integer - a hash computed for *ik. For equal keys the hash values are
  guaranteed to be equal.
*/
int int_key_hash(void* ik);
//@ requires [?f]int_k_p(ik, ?k);
//@ ensures [f]int_k_p(ik, k) &*& result == int_hash(k);

/**
   Hash function for ext_key's.
   Necessary for DoubleMap, hence the generalized signature.

   @param ek - pointer to the ext_key.
   @returns integer - a hash computed for *ek. For equal keys the hash values are
   guaranteed to be equal.
*/
int ext_key_hash(void* ek);
//@ requires [?f]ext_k_p(ek, ?k);
//@ ensures [f]ext_k_p(ek, k) &*& result == ext_hash(k);

/**
   Free the resources, acquired by the flow ID. In practice, does nothing.
   Necessary for DoubleMap, hence the generalized signature.
   It does not free memory itself.

   @param flwp - pointer to the flow to be destroyed.
*/
void flow_destroy(void* flwp);
//@ requires flw_p(flwp, ?flw);
//@ ensures chars(flwp, sizeof(struct flow), _);

/**
   Given the flow ID, get the internal and external keys.
   Necessary for DoubleMap, hence the generalized signature.

   @param flwp - the pointer to the flow ID.
   @param ikpp - the output pointer for the internal key extracted from the flow.
   @param ekpp - the output pointer for the external key extracted from the flow.
*/
void flow_extract_keys(void* flwp, void** ikpp, void** ekpp);
//@ requires [?f]flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures [f]flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
            true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/

/**
   The opposite of flow_extract_keys. In practice does nothing.
   Necessary for DoubleMap, hence the generalized signature.

   @param flwp - the pointer to the flow ID.
   @param ikp - pointer to the internal key, must be the one extracted
                previously.
   @param ekp - pointer to the external key, must be the one extracted
                previously.
*/
void flow_pack_keys(void* flwp, void* ikp, void* ekp);
/*@ requires [?f]flow_p(flwp, ?flw) &*&
             [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures [f]flw_p(flwp, flw);

/**
   Copy the flow ID.
   Necessary for DoubleMap, hence the generalized signature.

   @param dst - output pointer for the copy of the flow. Must point to
                a preallocated sufficient memory chunk.
   @param src - the flow to be copied.
*/
void flow_cpy(char* dst, void* src);
//@ requires [?fr]flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures [fr]flw_p(src, f) &*& flw_p((void*)dst, f);

#endif //_FLOW_H_INCLUDED_
