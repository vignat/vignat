#include <stdbool.h>
#include <string.h>
#include <limits.h>

#include "include_ignored_by_verifast.h"

#include "flow.h"
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

static long long wrap(long long x)
//@ requires true;
//@ ensures result == _wrap(x) &*& INT_MIN <= result &*& result <= INT_MAX;
{
  //@ div_rem(x, INT_MAX);
  return x % INT_MAX;
}

int int_key_hash(void* key)
//@ requires [?f]int_k_p(key, ?k);
//@ ensures [f]int_k_p(key, k) &*& result == int_hash(k);
{
  struct int_key* ik = key;

  long long hash = ik->int_src_port;
  hash *= 31;

  hash += ik->dst_port;
  hash *= 31;

  hash += ik->int_src_ip;
  hash *= 31;

  hash += ik->dst_ip;
  hash *= 31;

  hash += ik->int_device_id;
  hash *= 31;

  hash += ik->protocol;

  hash = wrap(hash);

  return (int) hash;
}

int ext_key_hash(void* key)
//@ requires [?f]ext_k_p(key, ?k);
//@ ensures [f]ext_k_p(key, k) &*& result == ext_hash(k);
{
  struct ext_key* ek = key;

  long long hash = ek->ext_src_port;
  hash *= 31;

  hash += ek->dst_port;
  hash *= 31;

  hash += ek->ext_src_ip;
  hash *= 31;

  hash += ek->dst_ip;
  hash *= 31;

  hash += ek->ext_device_id;
  hash *= 31;

  hash += ek->protocol;

  hash = wrap(hash);

  return (int) hash;
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
}

#ifdef KLEE_VERIFICATION

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

int flow_consistency(void* key_a, void* key_b,
                     int index, void* value) {
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
    ( 0 <= flow->int_device_id ) &
          (flow->int_device_id < RTE_MAX_ETHPORTS ) &
    ( 0 <= flow->ext_device_id ) & //FIXME: Klee translates this to signed variable
          (flow->ext_device_id < RTE_MAX_ETHPORTS ) &
    ( ext_key->ext_device_id == flow->ek.ext_device_id ) &
    ( ext_key->ext_device_id == flow->ext_device_id ) &
    ( int_key->int_device_id == flow->ik.int_device_id ) &
    ( int_key->int_device_id == flow->int_device_id ) &
    ( flow->int_device_id != flow->ext_device_id ) &
    ( ext_key->ext_src_port == starting_port + index) &
    ( flow->ext_src_port == starting_port + index ) &
    ( flow->ek.ext_src_port == starting_port + index );
    //(0 == memcmp(ext_key, &flow->ek, sizeof(struct ext_key)));
}
#endif//KLEE_VERIFICATION
