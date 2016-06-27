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
//@ requires [?f1]int_k_p(a, ?ak) &*& [?f2]int_k_p(b, ?bk);
//@ ensures [f1]int_k_p(a, ak) &*& [f2]int_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
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
//@ requires [?f1]ext_k_p(a, ?ak) &*& [?f2]ext_k_p(b, ?bk);
//@ ensures [f1]ext_k_p(a, ak) &*& [f2]ext_k_p(b, bk) &*& (0 == result ? (ak != bk) : (ak == bk));
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
//@ requires [?f]int_k_p(key, ?k);
//@ ensures [f]int_k_p(key, k) &*& result == int_hash(k);
{
  struct int_key* ik = key;
  uint32_t int_src_port = ik->int_src_port;
  uint32_t hash = int_src_port ^ ik->dst_port ^ ik->int_src_ip ^
                  ik->dst_ip ^ ik->int_device_id ^ ik->protocol;
  return ovf_cast(hash);
}

int ext_key_hash(void* key)
//@ requires [?f]ext_k_p(key, ?k);
//@ ensures [f]ext_k_p(key, k) &*& result == ext_hash(k);
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
//@ requires [?f]flw_p(flwp, ?flw) &*& *ikpp |-> _ &*& *ekpp |-> _;
/*@ ensures [f]flow_p(flwp, flw) &*& *ikpp |-> ?ikp &*& *ekpp |-> ?ekp &*&
            [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
            true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
            ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
{
  //@ open [f]flw_p(flwp, flw);
  struct flow* fp = flwp;
  *ikpp = &fp->ik;
  *ekpp = &fp->ek;
  //@ close [f]flow_p(flwp, flw);
}

void flow_pack_keys(void* flwp, void* ikp, void* ekp)
/*@ requires [?f]flow_p(flwp, ?flw) &*&
             [f]int_k_p(ikp, ?ik) &*& [f]ext_k_p(ekp, ?ek) &*&
             true == flow_keys_offsets_fp(flwp, ikp, ekp) &*&
             ik == flw_get_ik(flw) &*& ek == flw_get_ek(flw); @*/
//@ ensures [f]flw_p(flwp, flw);
{
  IGNORE(flwp);
  IGNORE(ikp);
  IGNORE(ekp);
  //@ open flow_p(flwp, flw);
}

void flow_cpy(char* dst, void* src)
//@ requires [?fr]flw_p(src, ?f) &*& dst[0..sizeof(struct flow)] |-> _;
//@ ensures [fr]flw_p(src, f) &*& flw_p((void*)dst, f);
{
  struct flow* source = src;
  struct flow* destination = (void*)dst;
  //@ close_struct(destination);
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
//@ ensures chars(flwp, sizeof(struct flow), _);
{
  IGNORE(flwp);
  //do nothing
  //@ open flw_p(flwp, _);
  //@ open_struct((struct flow*)flwp);
  // @ flow_to_bytes(flwp);
}

