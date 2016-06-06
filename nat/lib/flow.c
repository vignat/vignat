#include <string.h>
#include <limits.h>

#include "flow.h"
#include "include_ignored_by_verifast.h"
#include "ignore.h"

#ifdef KLEE_VERIFICATION
#  define AND(x,y) ((x)&(y))
#  define TO_INT(x) (x)
#else //KLEE_VERIFICATION
#  define AND(x,y) ((x)&&(y))
#  define TO_INT(x) (x ? 1 : 0)
#endif //KLEE_VERIFICATION

int int_key_eq(void* a, void* b)
//@ requires int_k_p(a, ?ak) &*& int_k_p(b, ?bk);
//@ ensures int_k_p(a, ak) &*& int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
{
  struct int_key* k1 = a;
  struct int_key* k2 = b;
  bool rez =
    AND(k1->int_src_port  == k2->int_src_port,
    AND(k1->dst_port      == k2->dst_port,
    AND(k1->int_src_ip    == k2->int_src_ip,
    AND(k1->dst_ip        == k2->dst_ip,
    AND(k1->int_device_id == k2->int_device_id,
       (k1->protocol      == k2->protocol))))));
  return TO_INT(rez);
}

int ext_key_eq(void* a, void* b)
//@ requires ext_k_p(a, ?ak) &*& ext_k_p(b, ?bk);
//@ ensures ext_k_p(a, ak) &*& ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
{
  struct ext_key* k1 = a;
  struct ext_key* k2 = b;
  bool rez =
    AND(k1->ext_src_port  == k2->ext_src_port,
    AND(k1->dst_port      == k2->dst_port,
    AND(k1->ext_src_ip    == k2->ext_src_ip,
    AND(k1->dst_ip        == k2->dst_ip,
    AND(k1->ext_device_id == k2->ext_device_id,
       (k1->protocol      == k2->protocol))))));
  return TO_INT(rez);
}

static int ovf_cast(uint32_t x)
//@ requires true;
//@ ensures x <= INT_MAX ? result == x : result == x - INT_MAX - 1;
{
  uint32_t mx = INT_MAX;
  if (x <= INT_MAX) return (int)x;
  //@ assert x <= UINT_MAX;
  //@ assert UINT_MAX == 2*INT_MAX + 1;
  //@ assert x <= 2*INT_MAX + 1;
  // TODO: Obviously??
  //@ assert (x - INT_MAX - 1 <= INT_MAX);
  uint32_t rez = x - mx - 1;
  return (int)rez;
}

int int_key_hash(void* key)
//@ requires int_k_p(key, ?k);
//@ ensures int_k_p(key, k) &*& result == int_hash(k);
{
  struct int_key* ik = key;
  uint32_t int_src_port = ik->int_src_port;
  uint32_t hash = int_src_port ^ ik->dst_port ^ ik->int_src_ip ^
                  ik->dst_ip ^ ik->int_device_id ^ ik->protocol;
  return ovf_cast(hash);
}

int ext_key_hash(void* key)
//@ requires ext_k_p(key, ?k);
//@ ensures ext_k_p(key, k) &*& result == ext_hash(k);
{
  struct ext_key* ek = key;
  uint32_t ext_src_port = ek->ext_src_port;
  uint32_t hash = ext_src_port ^ ek->dst_port ^ ek->ext_src_ip ^
                  ek->dst_ip ^ ek->ext_device_id ^ ek->protocol;
  return ovf_cast(hash);
}

//@ fixpoint bool my_offset(struct flow* fp, struct int_key* ik, struct ext_key* ek) { return &(fp->ik) == ik && &(fp->ek) == ek; }

/*@
  fixpoint bool flow_keys_offsets_fp1(struct flow* fp,
                                      struct int_key* ik,
                                      struct ext_key* ek) {
    return &(fp->ek) == ek;
  }


@*/

void flow_extract_keys(void* flwp, void** ikpp, void** ekpp)
//@ requires flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            int_k_p(ikp, ?ik) &*& ext_k_p(ekp, ?ek) &*&
            true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
{
  //@ open flw_p(flwp, flw);
  struct flow* fp = flwp;
  *ikpp = &fp->ik;
  *ekpp = &fp->ek;
  //@ close flow_p(flwp, flw);
}

void flow_pack_keys(void* flwp, void* ikp, void* ekp)
/*@ requires flow_p(flwp, ?flw) &*& int_k_p(ikp, ?ik) &*& ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures flw_p(flwp, flw);
{
  IGNORE(flwp);
  IGNORE(ikp);
  IGNORE(ekp);
  //@ open flow_p(flwp, flw);
}

/*@

  fixpoint list<char> chars_of_short(int x);
  fixpoint bool char_within_limits(char c);

  lemma void chars_within_limits_nil();
  requires true;
  ensures true == chars_within_limits(nil);

  lemma void chars_within_limits_uncons(char hd, list<char> tl);
  requires true == chars_within_limits(cons(hd,tl));
  ensures true == chars_within_limits(tl) &*&
          true == char_within_limits(hd);

  lemma void chars_within_limits_cons(char hd, list<char> tl);
  requires true == chars_within_limits(tl) &*&
           true == char_within_limits(hd);
  ensures true == chars_within_limits(cons(hd,tl));

  lemma void chars_within_limits_distr(int n, list<char> chs)
  requires true == chars_within_limits(chs) &*&
           0 <= n &*& n <= length(chs);
  ensures true == chars_within_limits(chs) &*&
          true == chars_within_limits(take(n, chs)) &*&
          true == chars_within_limits(drop(n, chs));
  {
    switch(chs){
      case nil: return;
      case cons(h,t):
        if (n==0) {
          chars_within_limits_nil();
        } else {
          chars_within_limits_uncons(h,t);
          chars_within_limits_distr(n-1, t);
          chars_within_limits_cons(h, take(n-1,t));
        }
    }
  }

  lemma void chars_within_limits_append(list<char> chs1, list<char> chs2)
  requires true == chars_within_limits(chs1) &*&
           true == chars_within_limits(chs2);
  ensures true == chars_within_limits(append(chs1, chs2));
  {
    switch(chs1) {
      case nil: return;
      case cons(h,t):
        chars_within_limits_uncons(h,t);
        chars_within_limits_append(t,chs2);
        chars_within_limits_cons(h, append(t,chs2));
    }
  }

  fixpoint list<char> chars_of_ik(int_k ik) {
    switch(ik) { case ikc(isp, dp, isip, dip, idid, prtc):
      return
        append(chars_of_short(isp), append(chars_of_short(dp),
        append(chars_of_int(isip), append(chars_of_int(dip),
        cons(idid, cons(prtc, nil))))));
    }
  }

  fixpoint list<char> chars_of_ek(ext_k ek) {
    switch(ek) { case ekc(esp, dp, esip, dip, edid, prtc):
      return
        append(chars_of_short(esp), append(chars_of_short(dp),
        append(chars_of_int(esip), append(chars_of_int(dip),
        cons(edid, cons(prtc, nil))))));
    }
  }

  lemma void chars_of_int_within_limits(int a);
  requires INT_MIN <= a &*& a <= INT_MAX;
  ensures true == chars_within_limits(chars_of_int(a));

  lemma void int_key_to_bytes(struct int_key* ik)
  requires int_k_p(ik, ?val);
  ensures chars((void*)ik, sizeof(struct int_key), chars_of_ik(val)) &*&
          chars_within_limits(chars_of_ik(val)) == true;
  {
    open int_k_p(ik, val);
    //open int_key_int_src_port(ik, ?isp);
    //open int_key_dst_port(ik, ?dp);
    open int_key_int_src_ip(ik, ?isip);
    open int_key_dst_ip(ik, ?dip);
    open int_key_int_device_id(ik, ?idid);
    open int_key_protocol(ik, ?prtc);
    assert int_key_dst_port(ik, ?dp);
    assume(false); //FIXME: https://github.com/verifast/verifast/issues/31
  }

  lemma void ext_key_to_bytes(struct ext_key* ek)
  requires ext_k_p(ek, ?val);
  ensures chars((void*)ek, sizeof(struct ext_key), chars_of_ek(val)) &*&
          chars_within_limits(chars_of_ek(val)) == true;
  {
    assume(false);
  }

  lemma void bytes_to_int_key(struct int_key* ik)
  requires chars((void*)ik, sizeof(struct int_key), ?chs);
  ensures int_k_p(ik, _);
  {
    assume(sizeof(struct int_key) == sizeof(uint16_t) + sizeof(uint16_t) +
           sizeof(uint32_t) + sizeof(uint32_t) + sizeof(uint8_t) + sizeof(uint8_t));
    chars_split((void*)ik, sizeof(uint16_t));
    close int_key_int_src_port(ik, _);
  }

  lemma void bytes_to_ext_key(void* ek);
  requires chars((void*)ek, sizeof(struct ext_key), ?chs);
  ensures ext_k_p(ek, _);

  lemma void bytes_to_flow(struct flow* f);
  requires chars((void*)f, sizeof(struct flow), ?chs);
  ensures 
  int_k_p(&f->ik, ?ik) &*&
  ext_k_p(&f->ek, ?ek) &*&
  f->int_src_port |-> ?isp &*&
  f->ext_src_port |-> ?esp &*&
  f->dst_port |-> ?dp &*&
  f->int_src_ip |-> ?isip &*&
  f->ext_src_ip |-> ?esip &*&
  f->dst_ip |-> ?dip &*&
  f->int_device_id |-> ?idid &*&
  f->ext_device_id |-> ?edid &*&
  f->protocol |-> ?prtc;

  @*/

void flow_cpy(char* dst, void* src)
//@ requires flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures flw_p(src, f) &*& flw_p((void*)dst, f);
{
  struct flow* source = src;
  struct flow* destination = (void*)dst;
  //@ bytes_to_flow(destination);
  destination->ik.int_src_port = source->ik.int_src_port;
  destination->ik.dst_port = source->ik.dst_port;
  destination->ik.int_src_ip = source->ik.int_src_ip;
  destination->ik.dst_ip = source->ik.dst_ip;
  destination->ik.int_device_id = source->ik.int_device_id;
  destination->ik.protocol = source->ik.protocol;
  destination->ek.ext_src_port = source->ek.ext_src_port;
  destination->ek.dst_port = source->ek.dst_port;
  destination->ek.ext_src_ip = source->ek.ext_src_ip;
  destination->ek.dst_ip = source->ek.dst_ip;
  destination->ek.ext_device_id = source->ek.ext_device_id;
  destination->ek.protocol = source->ek.protocol;
  destination->int_src_port = source->int_src_port;
  destination->ext_src_port = source->ext_src_port;
  destination->dst_port = source->dst_port;
  destination->int_src_ip = source->int_src_ip;
  destination->ext_src_ip = source->ext_src_ip;
  destination->dst_ip = source->dst_ip;
  destination->int_device_id = source->int_device_id;
  destination->ext_device_id = source->ext_device_id;
  destination->protocol = source->protocol;
}

void flow_destroy(void* flwp)
//@ requires flw_p(flwp, ?flw);
//@ ensures chars(flwp, sizeof(struct flow));
{
  IGNORE(flwp);
  //do nothing
}
