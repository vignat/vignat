#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include "double-map.h"

//@ #include "arith.gh"

struct DoubleMap {
  int value_size;

  uq_value_copy* cpy;
  uq_value_destr* dstr;

  uint8_t *values;

  int *bbs_a;
  void **kps_a;
  int *khs_a;
  int *chns_a;
  int *inds_a;
  map_keys_equality *eq_a;
  map_key_hash *hsh_a;

  int *bbs_b;
  void **kps_b;
  int *khs_b;
  int *chns_b;
  int *inds_b;
  map_keys_equality *eq_b;
  map_key_hash *hsh_b;

  dmap_extract_keys *exk;
  dmap_pack_keys *pk;

  int n_vals;
  int capacity;
  int keys_capacity;
};

/*@
  predicate valsp<t1,t2,vt>(void* values, int val_size,
                            predicate (void*,vt) fvp,
                            predicate (void*,vt) bvp,
                            list<pair<t1,void*> > addrs1,
                            list<pair<t2,void*> > addrs2,
                            fixpoint (vt,t1) vk1,
                            fixpoint (vt,t2) vk2,
                            fixpoint (void*,void*,void*,bool) rof,
                            int length, list<option<vt> > vals) =
     switch(vals) {
       case nil: return length == 0;
       case cons(h,t):
         return switch(h) {
           case none: return chars(values, val_size, _) &*&
                             valsp(values + val_size,
                                   val_size, fvp, bvp,
                                   addrs1, addrs2,
                                   vk1, vk2, rof,
                                   length-1, t);
           case some(v): return [0.5]fvp(values, v) &*&
                                [0.5]bvp(values, v) &*&
                                true == map_has_fp(addrs1, vk1(v)) &*&
                                true == map_has_fp(addrs2, vk2(v)) &*&
                                true == rof(values,
                                            map_get_fp(addrs1, vk1(v)),
                                            map_get_fp(addrs2, vk2(v))) &*&
                                valsp(values + val_size,
                                      val_size, fvp, bvp,
                                      addrs1, addrs2,
                                      vk1, vk2, rof,
                                      length-1, t);
         };
     };


  fixpoint bool insync_fp<t1,t2,vt>(list<option<vt> > vals,
                                    list<pair<t1,int> > m1,
                                    list<pair<t2,int> > m2,
                                    fixpoint (vt,t1) vk1,
                                    fixpoint (vt,t2) vk2,
                                    int start_index) {
    return dmap_self_consistent_fp(vals, m1, m2, vk1, vk2, start_index);
  }

  fixpoint bool no_extra_ptrs<t>(list<pair<t,void*> > addrs,
                                 list<pair<t,int> > m) {
    switch(addrs) {
      case nil: return true;
      case cons(h,t):
        return !map_has_fp(t, fst(h)) &&
               map_has_fp(m, fst(h)) && no_extra_ptrs(t, m);
    }
  }

  fixpoint bool no_such_keys<t1,t2,vt>(vt v, list<option<vt> > vals,
                                       fixpoint (vt,t1) vk1,
                                       fixpoint (vt,t2) vk2) {
    switch(vals) {
      case nil: return true;
      case cons(h,t): return no_such_keys(v, t, vk1, vk2) &&
        switch(h) {
          case none: return true;
          case some(x): return vk1(v) != vk1(x) && vk2(v) != vk2(x);
      };
    }
  }

  fixpoint bool all_keys_differ<t1,t2,vt>(list<option<vt> > vals,
                                          fixpoint (vt,t1) vk1,
                                          fixpoint (vt,t2) vk2) {
    switch(vals) {
      case nil: return true;
      case cons(h,t): return all_keys_differ(t, vk1, vk2) &&
        switch(h) {
          case none: return true;
          case some(v): return no_such_keys(v, t, vk1, vk2);
      };
    }
  }

  predicate dmappingp<t1,t2,vt>(dmap<t1,t2,vt> m,
                                predicate (void*;t1) keyp1,
                                predicate (void*;t2) keyp2,
                                fixpoint (t1,int) hsh1,
                                fixpoint (t2,int) hsh2,
                                predicate (void*;vt) full_vp,
                                predicate (void*,vt) bare_vp,
                                fixpoint (void*,void*,void*,bool) right_offsets,
                                int val_size,
                                fixpoint (vt,t1) vk1,
                                fixpoint (vt,t2) vk2,
                                fixpoint (t1,int,bool) recp1,
                                fixpoint (t2,int,bool) recp2,
                                struct DoubleMap* mp) =
    malloc_block_DoubleMap(mp) &*&
    mp->value_size |-> val_size &*&
    0 < val_size &*& val_size < 4096 &*&
    mp->cpy |-> ?v_cpy &*&
    [_]is_uq_value_copy<vt>(v_cpy, full_vp, val_size) &*&
    mp->dstr |-> ?v_destr &*&
    [_]is_uq_value_destr<vt>(v_destr, full_vp, val_size) &*&
    mp->values |-> ?values &*&
    valsp(values, val_size, full_vp, bare_vp,
          ?addrsa, ?addrsb, vk1, vk2, right_offsets,
          ?capacity, ?val_arr) &*&
    malloc_block(values, val_size*capacity) &*&
    mp->keys_capacity |-> ?keys_capacity &*&
    keys_capacity < CAPACITY_UPPER_LIMIT &*&
    mp->bbs_a |-> ?bbs_a &*& malloc_block_ints(bbs_a, keys_capacity) &*&
    mp->kps_a |-> ?kps_a &*& malloc_block_pointers(kps_a, keys_capacity) &*&
    mp->khs_a |-> ?khs_a &*& malloc_block_ints(khs_a, keys_capacity) &*&
    mp->inds_a |-> ?inds_a &*& malloc_block_ints(inds_a, keys_capacity) &*&
    mp->chns_a |-> ?chns_a &*& malloc_block_ints(chns_a, keys_capacity) &*&
    mapping(?ma, addrsa, keyp1, recp1, hsh1, keys_capacity,
            bbs_a, kps_a, khs_a, chns_a, inds_a) &*&
    mp->eq_a |-> ?eq_a &*&
    [_]is_map_keys_equality<t1>(eq_a, keyp1) &*&
    mp->hsh_a |-> ?hsh_a &*&
    [_]is_map_key_hash<t1>(hsh_a, keyp1, hsh1) &*&
    mp->bbs_b |-> ?bbs_b &*& malloc_block_ints(bbs_b, keys_capacity) &*&
    mp->kps_b |-> ?kps_b &*& malloc_block_pointers(kps_b, keys_capacity) &*&
    mp->khs_b |-> ?khs_b &*& malloc_block_ints(khs_b, keys_capacity) &*&
    mp->inds_b |-> ?inds_b &*& malloc_block_ints(inds_b, keys_capacity) &*&
    mp->chns_b |-> ?chns_b &*& malloc_block_ints(chns_b, keys_capacity) &*&
    mapping(?mb, addrsb, keyp2, recp2, hsh2, keys_capacity,
            bbs_b, kps_b, khs_b, chns_b, inds_b) &*&
    mp->eq_b |-> ?eq_b &*&
    [_]is_map_keys_equality<t2>(eq_b, keyp2) &*&
    mp->hsh_b |-> ?hsh_b &*&
    [_]is_map_key_hash<t2>(hsh_b, keyp2, hsh2) &*&
    mp->exk |-> ?exk &*&
    [_]is_dmap_extract_keys(exk, keyp1, keyp2, full_vp, bare_vp,
                            right_offsets, vk1, vk2) &*&
    mp->pk |-> ?pk &*&
    [_]is_dmap_pack_keys(pk, keyp1, keyp2, full_vp, bare_vp,
                         right_offsets, vk1, vk2) &*&
    mp->capacity |-> capacity &*&
    mp->n_vals |-> map_size_fp(ma) &*&
    0 <= capacity &*& capacity <= keys_capacity &*&
    values + val_size*capacity <= (void*)UINTPTR_MAX &*&
    true == insync_fp(val_arr, ma, mb, vk1, vk2, 0) &*&
    true == no_extra_ptrs(addrsa, ma) &*&
    true == no_extra_ptrs(addrsb, mb) &*&
    true == all_keys_differ(val_arr, vk1, vk2) &*&
    m == dmap(ma, mb, val_arr);
  @*/

/*@
  lemma void empty_valsp<t1,t2,vt>(void* values, int val_size,
                                   predicate (void*,vt) fvp,
                                   predicate (void*,vt) bvp,
                                   fixpoint (vt,t1) vk1,
                                   fixpoint (vt,t2) vk2,
                                   fixpoint (void*,void*,void*,bool) rof,
                                   nat len)
  requires chars(values, val_size*int_of_nat(len), _) &*&
           0 < val_size;
  ensures valsp(values, val_size, fvp, bvp,
                empty_map_fp<t1,void*>(),
                empty_map_fp<t2,void*>(),
                vk1, vk2, rof,
                int_of_nat(len),
                empty_vals_fp(len));
  {
    switch(len) {
      case zero:
        close valsp(values, val_size, fvp, bvp,
                    empty_map_fp<t1,void*>(),
                    empty_map_fp<t2,void*>(),
                    vk1, vk2, rof, 0, nil);
        return;
      case succ(n):
        assert 1 <= int_of_nat(len);
        assert val_size <= val_size*1;
        mul_mono(1, int_of_nat(len), val_size);
        mul_mono(int_of_nat(len) - 1, int_of_nat(n), val_size);
        mul_mono(int_of_nat(n), int_of_nat(len) - 1, val_size);
        assert val_size*(int_of_nat(len) - 1) == val_size*(int_of_nat(n));
        chars_split(values, val_size);
        empty_valsp(values + val_size, val_size, fvp, bvp,
                    vk1, vk2, rof, n);
        close valsp(values, val_size, fvp, bvp,
                    empty_map_fp<t1,void*>(),
                    empty_map_fp<t2,void*>(),
                    vk1, vk2, rof,
                    int_of_nat(len),
                    empty_vals_fp(len));
        return;
    }
  }
  @*/

/*@
  lemma void empty_insync<t1,t2,vt>(nat len, int capacity,
                                    fixpoint (vt,t1) vk1,
                                    fixpoint (vt,t2) vk2)
  requires true;
  ensures true == insync_fp(empty_vals_fp(len), empty_map_fp<t1,int>(),
                            empty_map_fp<t2,int>(), vk1, vk2,
                            capacity - int_of_nat(len));
  {
    switch(len) {
      case zero:
        return;
      case succ(n):
        empty_insync(n, capacity, vk1, vk2);
        return;
    }
  }
  @*/

/*@
  lemma void empty_all_keys_differ<t1,t2,vt>(nat len,
                                             fixpoint (vt,t1) vk1,
                                             fixpoint (vt,t2) vk2)
  requires true;
  ensures true == all_keys_differ(empty_vals_fp(len), vk1, vk2);
  {
    switch(len) {
      case zero: return;
      case succ(n):
        empty_all_keys_differ(n, vk1, vk2);
        return;
    }
  }
  @*/

int dmap_allocate/*@ <K1,K2,V> @*/
                 (map_keys_equality* eq_a, map_key_hash* hsh_a,
                  map_keys_equality* eq_b, map_key_hash* hsh_b,
                  int value_size, uq_value_copy* v_cpy,
                  uq_value_destr* v_destr,
                  dmap_extract_keys* dexk,
                  dmap_pack_keys* dpk,
                  int capacity,
                  int keys_capacity,
                  struct DoubleMap** map_out)
/*@ requires dmap_key_val_types<K1,K2,V>(_, _, _) &*&
             [_]is_map_keys_equality<K1>(eq_a, ?keyp1) &*&
             [_]is_map_key_hash<K1>(hsh_a, keyp1, ?hsh1) &*&
             [_]is_map_keys_equality<K2>(eq_b, ?keyp2) &*&
             [_]is_map_key_hash<K2>(hsh_b, keyp2, ?hsh2) &*&
             [_]is_uq_value_copy<V>(v_cpy, ?fvp, value_size) &*&
             [_]is_uq_value_destr<V>(v_destr, fvp, value_size) &*&
             [_]is_dmap_extract_keys(dexk, keyp1, keyp2, fvp,
                                     ?bvp, ?rof, ?vk1, ?vk2) &*&
             [_]is_dmap_pack_keys(dpk, keyp1, keyp2, fvp, bvp, rof, vk1, vk2) &*&
             dmap_record_property1<K1>(?recp1) &*&
             dmap_record_property2<K2>(?recp2) &*&
             *map_out |-> ?old_map_out &*&
             0 < value_size &*& value_size < 4096 &*&
             0 < capacity &*& capacity <= keys_capacity &*&
             keys_capacity < CAPACITY_UPPER_LIMIT; @*/
/*@ ensures result == 0 ?
            (*map_out |-> old_map_out) :
            (*map_out |-> ?mapp &*&
             result == 1 &*&
             dmappingp<K1,K2,V>(empty_dmap_fp(capacity), keyp1,
                                keyp2, hsh1, hsh2, fvp, bvp, rof, value_size,
                                vk1, vk2, recp1, recp2,
                                mapp)); @*/
{
  //@ open dmap_key_val_types(?def_k1, ?def_k2, ?def_val);
  //@ open dmap_record_property1(_);
  //@ open dmap_record_property2(_);
  struct DoubleMap* old_map_val = *map_out;
  struct DoubleMap* map_alloc = malloc(sizeof(struct DoubleMap));
  if (map_alloc == NULL) return 0;
  *map_out = (struct DoubleMap*) map_alloc;

  //@ mul_bounds(value_size, 4096, capacity, CAPACITY_UPPER_LIMIT);
  uint8_t* vals_alloc = malloc(value_size*capacity);
  if (vals_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->values = vals_alloc;
  int* bbs_a_alloc = malloc(sizeof(int)*keys_capacity);
  if (bbs_a_alloc == NULL) {
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_a = bbs_a_alloc;
  void** kps_a_alloc = malloc(sizeof(void*)*keys_capacity);
  if (kps_a_alloc == NULL) {
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_a = kps_a_alloc;
  int* khs_a_alloc = malloc(sizeof(int)*keys_capacity);
  if (khs_a_alloc == NULL) {
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_a = khs_a_alloc;
  int* chns_a_alloc = malloc(sizeof(int)*keys_capacity);
  if (chns_a_alloc == NULL) {
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->chns_a = chns_a_alloc;
  int* inds_a_alloc = malloc(sizeof(int)*keys_capacity);
  if (inds_a_alloc == NULL) {
    free(chns_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->inds_a = inds_a_alloc;
  int* bbs_b_alloc = malloc(sizeof(int)*keys_capacity);
  if (bbs_b_alloc == NULL) {
    free(inds_a_alloc);
    free(chns_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_b = bbs_b_alloc;
  void** kps_b_alloc = malloc(sizeof(void*)*keys_capacity);
  if (kps_b_alloc == NULL) {
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(chns_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_b = kps_b_alloc;
  int* khs_b_alloc = malloc(sizeof(int)*keys_capacity);
  if (khs_b_alloc == NULL) {
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(chns_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_b = khs_b_alloc;
  int* inds_b_alloc = malloc(sizeof(int)*keys_capacity);
  if (inds_b_alloc == NULL) {
    free(khs_b_alloc);
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(chns_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->inds_b = inds_b_alloc;
  int* chns_b_alloc = malloc(sizeof(int)*keys_capacity);
  if (chns_b_alloc == NULL) {
    free(inds_b_alloc);
    free(khs_b_alloc);
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(chns_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->chns_b = chns_b_alloc;

  (*map_out)->eq_a = eq_a;
  (*map_out)->hsh_a = hsh_a;
  (*map_out)->eq_b = eq_b;
  (*map_out)->hsh_b = hsh_b;
  (*map_out)->value_size = value_size;
  (*map_out)->cpy = v_cpy;
  (*map_out)->dstr = v_destr;
  (*map_out)->exk = dexk;
  (*map_out)->pk = dpk;
  (*map_out)->capacity = capacity;
  (*map_out)->keys_capacity = keys_capacity;

  //@ close map_key_type();
  //@ close map_key_hash(hsh1);
  //@ close map_record_property(recp1);
  map_impl_init((*map_out)->bbs_a, (*map_out)->eq_a,
                (*map_out)->kps_a, (*map_out)->khs_a, (*map_out)->chns_a,
                (*map_out)->inds_a,
                (*map_out)->keys_capacity);
  //@ close map_key_type();
  //@ close map_key_hash(hsh2);
  //@ close map_record_property(recp2);
  map_impl_init((*map_out)->bbs_b, (*map_out)->eq_b,
                (*map_out)->kps_b, (*map_out)->khs_b, (*map_out)->chns_b,
                (*map_out)->inds_b,
                (*map_out)->keys_capacity);

  (*map_out)->n_vals = 0;
  //@ chars_limits((void*)vals_alloc);
  /*@ empty_valsp(vals_alloc, value_size, fvp, bvp,
                  vk1, vk2, rof,
                  nat_of_int(capacity));
    @*/
  //@ empty_insync(nat_of_int(capacity), capacity, vk1, vk2);
  //@ empty_all_keys_differ(nat_of_int(capacity), vk1, vk2);
  /*@ close dmappingp<K1,K2,V>(empty_dmap_fp<K1,K2,V>(capacity), keyp1, keyp2,
                               hsh1, hsh2,
                               fvp, bvp, rof, value_size,
                               vk1, vk2, recp1, recp2, *map_out);
    @*/
  return 1;
}

/*@
  predicate hide_map_key_hash<kt>(map_key_hash* hsh, predicate (void*;kt) keyp,
                                  fixpoint (kt,int) hshfp) =
    is_map_key_hash<kt>(hsh, keyp, hshfp);

  predicate hide_mapping<kt>(list<pair<kt,int> > m,
                             list<pair<kt,void*> > addrs,
                             predicate (void*;kt) keyp,
                             fixpoint (kt,int,bool) recp,
                             fixpoint (kt,int) hash,
                             int cap,
                             int* busybits,
                             void** keyps,
                             int* k_hashes,
                             int* chns,
                             int* values) =
    mapping<kt>(m, addrs, keyp, recp, hash,
                cap, busybits, keyps, k_hashes, chns, values);
  @*/

int dmap_get_a/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map) &*&
             kp1(key, ?k1) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map) &*&
            kp1(key, k1) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k1_fp(m, k1) &*&
              true == rp1(k1, ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  map_key_hash *hsh_a = map->hsh_a;
  //@ map_key_hash *hsh_b = map->hsh_b;
  //@ assert [?x]is_map_key_hash(hsh_b, kp2, hsh2);
  //@ close [x]hide_map_key_hash(map->hsh_b, kp2, hsh2);
  int hash = hsh_a(key);
  //@ open [x]hide_map_key_hash(map->hsh_b, kp2, hsh2);
  int rez = map_impl_get(map->bbs_a, map->kps_a, map->khs_a, map->chns_a,
                         map->inds_a, key,
                         map->eq_a, hash, index,
                         map->keys_capacity);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  return rez;
}

int dmap_get_b/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map) &*&
             kp2(key, ?k2) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map) &*&
            kp2(key, k2) &*&
            (dmap_has_k2_fp(m, k2) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k2_fp(m, k2) &*&
              true == rp2(k2, ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  map_key_hash *hsh_b = map->hsh_b;
  //@ map_key_hash *hsh_a = map->hsh_a;
  //@ assert [?x]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  int hash = hsh_b(key);
  //@ open [x]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ int* bbs1 = map->bbs_a;
  //@ void** kps1 = map->kps_a;
  //@ int* khs1 = map->khs_a;
  //@ int* chns1 = map->chns_a;
  //@ int* vals1 = map->inds_a;
  /*@ assert mapping(?m1, ?addrs1, kp1, rp1, hsh1, ?cap,
                     bbs1, kps1, khs1, chns1, vals1);
    @*/
  /*@ close hide_mapping(m1, addrs1, kp1, rp1, hsh1, cap,
                         bbs1, kps1, khs1, chns1, vals1);
    @*/
  return map_impl_get(map->bbs_b, map->kps_b, map->khs_b, map->chns_b,
                      map->inds_b, key,
                      map->eq_b, hash, index,
                      map->keys_capacity);
  //@ open hide_mapping(_, _, _, _, _, _, _, _, _, _, _);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
}

/*@
  lemma void extract_value<t1,t2,vt>(void* values, list<option<vt> > vals, int i)
  requires valsp<t1,t2,vt>(values, ?vsz, ?fvp, ?bvp, ?addrs1, ?addrs2,
                           ?vk1, ?vk2, ?rof, ?len, vals) &*&
           0 <= i &*& i < len;
  ensures valsp<t1,t2,vt>(values, vsz, fvp, bvp,
                          addrs1, addrs2, vk1, vk2, rof,
                          i, take(i, vals)) &*&
          switch(nth(i, vals)) { case none : return chars(values+i*vsz, vsz, _);
                                 case some(x): return [0.5]fvp(values+i*vsz, x) &*&
                                                      [0.5]bvp(values+i*vsz, x) &*&
                                                      true ==
                                                      map_has_fp(addrs1, vk1(x)) &*&
                                                      true ==
                                                      map_has_fp(addrs2, vk2(x)) &*&
                                                      true ==
                                                      rof(values+i*vsz,
                                                          map_get_fp(addrs1,
                                                                     vk1(x)),
                                                          map_get_fp(addrs2,
                                                                     vk2(x))); } &*&
          valsp<t1,t2,vt>(values+(i+1)*vsz, vsz, fvp, bvp,
                          addrs1, addrs2, vk1, vk2, rof,
                          len-i-1, drop(i+1, vals));
  {
    open valsp(values, vsz, fvp, bvp,
               addrs1, addrs2, vk1, vk2,
               rof, len, vals);
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (i == 0) {
        } else {
          extract_value(values + vsz, t, i-1);
        }
    }
    close valsp(values, vsz, fvp, bvp,
                addrs1, addrs2, vk1, vk2, rof,
                i, take(i, vals));
  }
  @*/

/*@
  //workaround for https://github.com/verifast/verifast/issues/37
  predicate keep_rof(fixpoint (void*,void*,void*,bool) rof,
                     void* v, void* k1, void* k2) =
    true == rof(v, k1, k2);
    @*/

/*@
  lemma void glue_values<t1,t2,vt>(void* values, list<option<vt> > vals, int i)
  requires valsp<t1,t2,vt>(values, ?vsz, ?fvp, ?bvp,
                           ?addrs1, ?addrs2, ?vk1, ?vk2, ?rof,
                           i, take(i, vals)) &*&
           nth(i, vals) != none &*&
           [0.5]fvp(values+i*vsz, get_some(nth(i, vals))) &*&
           [0.5]bvp(values+i*vsz, get_some(nth(i, vals))) &*&
           true == map_has_fp(addrs1, vk1(get_some(nth(i, vals)))) &*&
           true == map_has_fp(addrs2, vk2(get_some(nth(i, vals)))) &*&
           true == rof(values+i*vsz,
                       map_get_fp(addrs1, vk1(get_some(nth(i, vals)))),
                       map_get_fp(addrs2, vk2(get_some(nth(i, vals))))) &*&
           valsp<t1,t2,vt>(values+(i+1)*vsz, vsz, fvp, bvp,
                           addrs1, addrs2, vk1, vk2, rof,
                           length(vals)-i-1, drop(i+1, vals)) &*&
           0 <= i &*& i < length(vals);
  ensures valsp<t1,t2,vt>(values, vsz, fvp, bvp,
                          addrs1, addrs2, vk1, vk2, rof,
                          length(vals), vals);
  {
    void* xxx = values + i*vsz;
    void* aaa = map_get_fp(addrs1, vk1(get_some(nth(i, vals))));
    void* bbb = map_get_fp(addrs2, vk2(get_some(nth(i, vals))));
  assert true == rof(xxx,
                     aaa,
                     bbb);
    close keep_rof(rof, xxx, aaa, bbb);
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        open keep_rof(rof, xxx, aaa, bbb);
        assert true == rof(xxx,
                           aaa,
                           bbb);
        assert true == rof(values+i*vsz,
                           map_get_fp(addrs1, vk1(get_some(nth(i, vals)))),
                           map_get_fp(addrs2, vk2(get_some(nth(i, vals)))));
        close keep_rof(rof, values+i*vsz,
                       map_get_fp(addrs1, vk1(get_some(nth(i, vals)))),
                       map_get_fp(addrs2, vk2(get_some(nth(i, vals)))));
        open valsp(values, vsz, fvp, bvp,
                   addrs1, addrs2, vk1, vk2, rof,
                   i, take(i, vals));
        open keep_rof(rof, values+i*vsz,
                       map_get_fp(addrs1, vk1(get_some(nth(i, vals)))),
                       map_get_fp(addrs2, vk2(get_some(nth(i, vals)))));
        assert true == rof(values+i*vsz,
                           map_get_fp(addrs1, vk1(get_some(nth(i, vals)))),
                           map_get_fp(addrs2, vk2(get_some(nth(i, vals)))));
        if (i == 0) {
        } else {
          assert(values + vsz + (i-1)*vsz == values + i*vsz);
          assert(get_some(nth(i-1,t)) == get_some(nth(i,vals)));
          assert true == rof(values+i*vsz,
                             map_get_fp(addrs1, vk1(get_some(nth(i, vals)))),
                             map_get_fp(addrs2, vk2(get_some(nth(i, vals)))));
          assert true == rof(values + vsz + (i-1)*vsz,
                             map_get_fp(addrs1, vk1(get_some(nth(i-1, t)))),
                             map_get_fp(addrs2, vk2(get_some(nth(i-1, t)))));
          glue_values(values + vsz, t, i-1);
        }
        close valsp(values, vsz, fvp, bvp,
                    addrs1, addrs2, vk1, vk2, rof,
                    length(vals), vals);
    }
  }
  @*/

/*@
  lemma void update_values_hole<t1,t2,vt>(void* values, list<option<vt> > vals, int i)
  requires valsp<t1,t2,vt>(values, ?vsz, ?fvp, ?bvp,
                           ?addrs1, ?addrs2, ?vk1, ?vk2, ?rof,
                           i, take(i, vals)) &*&
           nth(i, vals) == none &*&
           chars(values+i*vsz, vsz, _) &*&
           valsp<t1,t2,vt>(values+(i+1)*vsz, vsz, fvp, bvp,
                           addrs1, addrs2, vk1, vk2, rof,
                           length(vals)-i-1, drop(i+1, vals)) &*&
           0 <= i &*& i < length(vals);
  ensures valsp<t1,t2,vt>(values, vsz, fvp, bvp,
                          addrs1, addrs2, vk1, vk2, rof,
                          length(vals), vals);
  {
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        open valsp(values, vsz, fvp, bvp,
                   addrs1, addrs2, vk1, vk2, rof,
                   i, take(i, vals));
        if (i == 0) {
        } else {
          update_values_hole(values + vsz, t, i-1);
        }
        close valsp(values, vsz, fvp, bvp,
                    addrs1, addrs2, vk1, vk2, rof,
                    length(vals), vals);
    }
  }
  @*/
/*@
  lemma void vals_len_is_cap<t1,t2,vt>(list<option<vt> > vals, int capacity)
  requires valsp<t1,t2,vt>(?values, ?vsz, ?fvp, ?bvp,
                           ?addrs1, ?addrs2, ?vk1, ?vk2, ?rof,
                           capacity, vals);
  ensures valsp<t1,t2,vt>(values, vsz, fvp, bvp,
                          addrs1, addrs2, vk1, vk2, rof,
                          capacity, vals) &*&
          length(vals) == capacity;
  {
    open valsp(values, vsz, fvp, bvp,
               addrs1, addrs2, vk1, vk2, rof,
               capacity, vals);
    switch(vals) {
      case nil:
        break;
      case cons(h,t):
        vals_len_is_cap(t, capacity-1);
    }
    close valsp(values, vsz, fvp, bvp,
                addrs1, addrs2, vk1, vk2, rof,
                capacity, vals);
  }
  @*/

/*@
  lemma void map_erase_monotonic_len<kt,vt>(list<pair<kt,vt> > m, kt k)
  requires true;
  ensures map_size_fp(map_erase_fp(m, k)) <= map_size_fp(m);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != k) map_erase_monotonic_len(t, k);
    }
  }

  lemma void map_erase_gradual_len<kt,vt>(list<pair<kt,vt> > m, kt k)
  requires true;
  ensures map_size_fp(m) <= map_size_fp(map_erase_fp(m, k)) + 1;
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != k) map_erase_gradual_len(t, k);
    }
  }
  @*/

/*@
  lemma void insync_map_size_bound<t1,t2,vt>(list<option<vt> > vals,
                                             list<pair<t1,int> > m1,
                                             list<pair<t2,int> > m2,
                                             fixpoint (vt,t1) vk1,
                                             fixpoint (vt,t2) vk2,
                                             int capacity)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals));
  ensures map_size_fp(m1) <= length(vals) &*&
          map_size_fp(m2) <= length(vals);
  {
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_map_size_bound(t, m1, m2, vk1, vk2, capacity);
            return;
          case some(v):
            insync_map_size_bound(t, map_erase_fp(m1, vk1(v)),
                                  map_erase_fp(m2, vk2(v)),
                                  vk1, vk2, capacity);
            map_erase_gradual_len(m1, vk1(v));
            map_erase_gradual_len(m2, vk2(v));
            return;
        }
    }
  }

  lemma void insync_has_not_nonfull<t1,t2,vt>(list<option<vt> > vals,
                                              list<pair<t1,int> > m1,
                                              list<pair<t2,int> > m2,
                                              fixpoint (vt,t1) vk1,
                                              fixpoint (vt,t2) vk2,
                                              int capacity,
                                              int index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals)) &*&
           0 <= index &*& index < length(vals) &*&
           nth(index, vals) == none;
  ensures map_size_fp(m1) < length(vals) &*&
          map_size_fp(m2) < length(vals);
  {
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        if (index == 0) {
          insync_map_size_bound(t, m1, m2, vk1, vk2, capacity);
        } else {
          switch(h) {
            case none:
              insync_has_not_nonfull(t, m1, m2, vk1, vk2, capacity, index-1);
              return;
            case some(v):
              insync_has_not_nonfull(t, map_erase_fp(m1, vk1(v)),
                                     map_erase_fp(m2, vk2(v)),
                                     vk1, vk2, capacity, index-1);
              map_erase_gradual_len(m1, vk1(v));
              map_erase_gradual_len(m2, vk2(v));
              return;
          }
        }
    }
  }
  @*/

/*@
  lemma void map_erase_preserves_not_has<t>(list<pair<t,int> > m, t k1, t k2)
  requires false == map_has_fp(m, k2);
  ensures false == map_has_fp(map_erase_fp(m, k1), k2);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (fst(h) != k1) map_erase_preserves_not_has(t, k1, k2);
    }
  }
  @*/

/*@
  lemma void map_put_erase_swap<t>(list<pair<t,int> > m, t k1, int v, t k2)
  requires k1 != k2;
  ensures map_erase_fp(map_put_fp(m, k1, v), k2) ==
          map_put_fp(map_erase_fp(m, k2), k1, v);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != k2) {
          map_put_erase_swap(t, k1, v, k2);
        }
    }
  }
  @*/

/*@
  lemma void update_insync<t1,t2,vt>(list<option<vt> > vals,
                                     list<pair<t1,int> > m1,
                                     list<pair<t2,int> > m2,
                                     int index,
                                     vt v,
                                     fixpoint (vt,t1) vk1,
                                     fixpoint (vt,t2) vk2,
                                     int capacity)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals)) &*&
           0 <= index &*& index < length(vals) &*&
           nth(index, vals) == none &*&
           false == map_has_fp(m1, vk1(v)) &*&
           false == map_has_fp(m2, vk2(v));
  ensures true == insync_fp(update(index, some(v), vals),
                            map_put_fp(m1, vk1(v), index + capacity - length(vals)),
                            map_put_fp(m2, vk2(v), index + capacity - length(vals)),
                            vk1, vk2, capacity - length(vals));
  {
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        if (index == 0) {
          tail_of_update_0(vals, some(v));
          head_update_0(some(v), vals);
          cons_head_tail(update(index, some(v), vals));
        } else {
          switch(h) {
            case none:
              update_insync(t, m1, m2, index-1, v, vk1, vk2, capacity);
              break;
            case some(x):
              map_erase_preserves_not_has(m1, vk1(x), vk1(v));
              map_erase_preserves_not_has(m2, vk2(x), vk2(v));
              update_insync(t, map_erase_fp(m1, vk1(x)),
                            map_erase_fp(m2, vk2(x)),
                            index-1, v, vk1, vk2, capacity);
              map_put_erase_swap(m1, vk1(v), index + capacity - length(vals), vk1(x));
              map_put_erase_swap(m2, vk2(v), index + capacity - length(vals), vk2(x));
              break;
          }
          return;
        }
    }
  }
  @*/

/*@
  lemma void put_unrelevant_preserves_no_such_keys<t1,t2,vt>
             (vt v, int i, vt x,
              list<option<vt> > vals,
              fixpoint (vt,t1) vk1,
              fixpoint (vt,t2) vk2)
  requires true == no_such_keys(x, vals, vk1, vk2) &*&
           0 <= i &*& i < length(vals) &*&
           vk1(v) != vk1(x) &*& vk2(v) != vk2(x);
  ensures true == no_such_keys(x, update(i, some(v), vals), vk1, vk2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (i == 0) {
        } else {
          put_unrelevant_preserves_no_such_keys(v, i-1, x, t, vk1, vk2);
          update_tail_tail_update(h, t, i, some(v));
          switch(h) {
            case none: break;
            case some(hv): break;
          }
        }
    }
  }

  lemma void put_preserves_all_keys_differ<t1,t2,vt>(vt v, int i,
                                                     list<option<vt> > vals,
                                                     fixpoint (vt,t1) vk1,
                                                     fixpoint (vt,t2) vk2)
  requires true == all_keys_differ(vals, vk1, vk2) &*&
           0 <= i &*& i < length(vals) &*&
           true == no_such_keys(v, vals, vk1, vk2);
  ensures true == all_keys_differ(update(i, some(v), vals), vk1, vk2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (i == 0) {
          switch(h) {
            case none: break;
            case some(x): break;
          }
          assert true == all_keys_differ(t, vk1, vk2);
          assert true == no_such_keys(v, t, vk1, vk2);
        } else {
          switch(h) {
            case none: break;
            case some(x):
              assert vk1(v) != vk1(x);
              assert vk2(v) != vk2(x);
              put_unrelevant_preserves_no_such_keys(v, i-1, x, t, vk1, vk2);
              break;
          }
          put_preserves_all_keys_differ(v, i-1, t, vk1, vk2);
        }
    }
  }
  @*/

/*@
  lemma void valsp_addrs_put<t1,t2,vt>(void* values, list<option<vt> > vals,
                                       vt v,
                                       list<pair<t1,void*> > addrs1,
                                       list<pair<t2,void*> > addrs2,
                                       fixpoint (vt,t1) vk1,
                                       fixpoint (vt,t2) vk2,
                                       void* key_a,
                                       void* key_b)
   requires valsp(values, ?vsz, ?fvp, ?bvp, addrs1, addrs2,
                  vk1, vk2, ?rof, ?len, vals) &*&
            false == map_has_fp(addrs1, vk1(v)) &*&
            false == map_has_fp(addrs2, vk2(v));
   ensures valsp(values, vsz, fvp, bvp,
                 map_put_fp(addrs1, vk1(v), key_a),
                 map_put_fp(addrs2, vk2(v), key_b),
                 vk1, vk2, rof, len, vals);
   {
     open valsp(values, vsz, fvp, bvp, addrs1, addrs2, vk1, vk2, rof, len, vals);
     switch(vals) {
       case nil: break;
       case cons(h,t):
         assert h != some(v);
         switch(h) {
           case none: break;
           case some(x):
             assert x != v;
             assert true == map_has_fp(addrs1, vk1(x));
             assert false == map_has_fp(addrs1, vk1(v));
             assert vk1(x) != vk1(v);
             assert map_get_fp(addrs1, vk1(x)) ==
                    map_get_fp(map_put_fp(addrs1, vk1(v), key_a), vk1(x));
         }
         valsp_addrs_put(values+vsz, t, v, addrs1, addrs2,
                         vk1, vk2, key_a, key_b);
     }
     close valsp(values, vsz, fvp, bvp,
                 map_put_fp(addrs1, vk1(v), key_a),
                 map_put_fp(addrs2, vk2(v), key_b),
                 vk1, vk2, rof, len, vals);
   }
   @*/

/*@
  lemma void no_extra_ptrs_has_not<t>(list<pair<t, int> > m,
                                      list<pair<t, void*> > addrs,
                                      t k)
  requires true == no_extra_ptrs(addrs, m) &*&
           false == map_has_fp(m, k);
  ensures false == map_has_fp(addrs, k);
  {
    switch(addrs) {
      case nil: return;
      case cons(h,t):
        no_extra_ptrs_has_not(m, t, k);
    }
  }
  @*/

/*@

  lemma void map_put_preserves_no_extra_ptrs<t>(list<pair<t, int> > m,
                                                list<pair<t, void*> > addrs,
                                                t k, int v)
  requires true == no_extra_ptrs(addrs, m);
  ensures true == no_extra_ptrs(addrs, map_put_fp(m, k, v));
  {
    switch(addrs) {
      case nil: return;
      case cons(h,t):
        map_put_preserves_no_extra_ptrs(m, t, k, v);
    }
  }

  lemma void put_preserves_no_extra_ptrs<t>(list<pair<t, int> > m,
                                            list<pair<t, void*> > addrs,
                                            t k, int v, void* addr)
  requires true == no_extra_ptrs(addrs, m) &*&
           false == map_has_fp(addrs, k);
  ensures true == no_extra_ptrs(map_put_fp(addrs, k, addr), map_put_fp(m, k, v));
  {
    map_put_preserves_no_extra_ptrs(m, addrs, k, v);
  }
  @*/

/*@
  lemma void insync_no_keys<t1,t2,vt>(list<option<vt> > vals,
                                      vt v,
                                      list<pair<t1, int> > m1,
                                      list<pair<t2, int> > m2,
                                      fixpoint (vt,t1) vk1,
                                      fixpoint (vt,t2) vk2,
                                      int capacity)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals)) &*&
           false == map_has_fp(m1, vk1(v)) &*&
           false == map_has_fp(m2, vk2(v));
  ensures true == no_such_keys(v, vals, vk1, vk2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_no_keys(t, v, m1, m2, vk1, vk2, capacity);
            break;
          case some(x):
            map_erase_preserves_not_has(m1, vk1(x), vk1(v));
            map_erase_preserves_not_has(m2, vk2(x), vk2(v));
            insync_no_keys(t, v, map_erase_fp(m1, vk1(x)),
                           map_erase_fp(m2, vk2(x)),
                           vk1, vk2, capacity);
        }
    }
  }
  @*/

/*@
  predicate hide_half_bvp<vt>(predicate (void*,vt) bvp, void* addr, vt v) =
    [0.5]bvp(addr,v);
  @*/

int dmap_put/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* value, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map) &*&
             fvp(value, ?v) &*&
             true == rp1(vk1(v), index) &*&
             true == rp2(vk2(v), index) &*&
             false == dmap_index_used_fp(m, index) &*&
             false == dmap_has_k1_fp(m, vk1(v)) &*&
             false == dmap_has_k2_fp(m, vk2(v)) &*&
             0 <= index &*& index < dmap_cap_fp(m); @*/
/*@ ensures result == 1 &*&
            dmappingp<K1,K2,V>(dmap_put_fp(m, index, v, vk1, vk2),
                               kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map) &*&
            fvp(value, v);@*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  //@ void* values = map->values;
  /*@ assert valsp(values, vsz, fvp, bvp,
                   ?addrs1, ?addrs2, vk1, vk2, rof,
                   ?cap, ?vals);
                   @*/
  //@ vals_len_is_cap<K1,K2,V>(vals, cap);
  void* key_a = 0;
  void* key_b = 0;
  //@ mul_bounds(index, cap, vsz, 4096);
  //@ mul_mono_strict(index, cap, vsz);
  //@ extract_value<K1,K2,V>(map->values, vals, index);
  void* my_value = map->values + index*map->value_size;
  uq_value_copy* cpy = map->cpy;
  cpy(my_value, value);

  dmap_extract_keys *exk = map->exk;
  exk(my_value, &key_a, &key_b);

  map_key_hash *hsh_a = map->hsh_a;
  int hash1 = hsh_a(key_a);

  /*@ assert mapping(?m1, addrs1, kp1, rp1, hsh1, ?keys_cap,
                     ?bbs1, ?kps1, ?khs1, ?chns1, ?vals1);
    @*/
  /*@ assert mapping(?m2, addrs2, kp2, rp2, hsh2, keys_cap,
                     ?bbs2, ?kps2, ?khs2, ?chns2, ?vals2);
    @*/
  //@ insync_has_not_nonfull(vals, m1, m2, vk1, vk2, cap, index);

  map_impl_put(map->bbs_a, map->kps_a, map->khs_a, map->chns_a,
               map->inds_a, key_a,
               hash1,
               index, map->keys_capacity);

  //@ assert [?x1]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x1]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ assert [?x2]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x2]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  map_key_hash *hsh_b = map->hsh_b;
  int hash2 = hsh_b(key_b);
  //@ open [x2]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ open [x1]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  /*@ close hide_mapping(map_put_fp(m1, vk1(v), index),
                         map_put_fp(addrs1, vk1(v), key_a),
                         kp1, rp1, hsh1, keys_cap, bbs1, kps1, khs1,
                         chns1, vals1);
    @*/
  map_impl_put(map->bbs_b, map->kps_b, map->khs_b, map->chns_b,
               map->inds_b, key_b,
               hash2,
               index, map->keys_capacity);
  /*@ open hide_mapping(_, _, kp1, rp1, hsh1, keys_cap, bbs1, kps1,
                        khs1, chns1, vals1);
    @*/
  ++map->n_vals;
  dmap_pack_keys *pk = map->pk;
  //@ close hide_half_bvp(bvp, my_value, v);
  pk(my_value, key_a, key_b);
  //@ open hide_half_bvp(bvp, my_value, v);
  //@ take_update_unrelevant(index, index, some(v), vals);
  //@ drop_update_unrelevant(index+1, index, some(v), vals);
  //@ nth_update(index, index, some(v), vals);
  //@ assert true == rof(values + index*vsz, key_a, key_b);
  //@ assert map_get_fp(map_put_fp(addrs1, (vk1(v)), key_a), vk1(v)) == key_a;
  //@ assert map_get_fp(map_put_fp(addrs2, (vk2(v)), key_b), vk2(v)) == key_b;
  //@ no_extra_ptrs_has_not(m1, addrs1, vk1(v));
  //@ no_extra_ptrs_has_not(m2, addrs2, vk2(v));
  //@ valsp_addrs_put(map->values, take(index, vals), v, addrs1, addrs2, vk1, vk2, key_a, key_b);
  //@ valsp_addrs_put(map->values + (index+1)*vsz, drop(index+1, vals), v, addrs1, addrs2, vk1, vk2, key_a, key_b);
  //@ glue_values(map->values, update(index, some(v), vals), index);

  //@ update_insync(vals, m1, m2, index, v, vk1, vk2, cap);
  //@ insync_no_keys(vals, v, m1, m2, vk1, vk2, cap);
  //@ put_preserves_all_keys_differ(v, index, vals, vk1, vk2);

  //@ put_preserves_no_extra_ptrs(m1, addrs1, vk1(v), index, key_a);
  //@ put_preserves_no_extra_ptrs(m2, addrs2, vk2(v), index, key_b);

  /*@ close dmappingp(dmap_put_fp(m, index, v, vk1, vk2),
                      kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  return 1;
}

void dmap_get_value/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index,
                                     void* value_out)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             chars(value_out, vsz, _) &*&
             0 <= index &*& index < dmap_cap_fp(m); @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map) &*&
            fvp(value_out, dmap_get_val_fp(m, index)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  //@ void* values = map->values;
  /*@ assert valsp(values, vsz, fvp, bvp,
                   ?addrs1, ?addrs2, vk1, vk2, rof,
                   ?cap, ?vals);
    @*/
  //@ vals_len_is_cap(vals, cap);
  //@ mul_bounds(index, cap, vsz, 4096);
  //@ mul_mono_strict(index, cap, vsz);
  //@ extract_value(map->values, vals, index);
  void* my_value = map->values + index*map->value_size;
  uq_value_copy* cpy = map->cpy;
  cpy(value_out, my_value);
  //@ glue_values(map->values, vals, index);
  /*@ close dmappingp(m,
                      kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
}

/*@
  lemma void map_erase_has_unrelevant<kt,vt>(list<pair<kt,vt> > m,
                                             kt k1, kt k2)
  requires k1 != k2;
  ensures map_has_fp(m, k2) == map_has_fp(map_erase_fp(m, k1), k2);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != k1) map_erase_has_unrelevant(t, k1, k2);
    }
  }

  lemma void map_erase_get_unrelevant<kt,vt>(list<pair<kt,vt> > m,
                                             kt k1, kt k2)
  requires k1 != k2;
  ensures map_get_fp(m, k2) == map_get_fp(map_erase_fp(m, k1), k2);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
      if (fst(h) != k1) map_erase_get_unrelevant(t, k1, k2);
    }
  }

  lemma void erase_addrs<t1,t2,vt>(void* values, list<option<vt> > vals,
                                   vt v,
                                   fixpoint (vt,t1) vk1,
                                   fixpoint (vt,t2) vk2)
  requires valsp<t1,t2,vt>(values, ?vsz, ?fvp, ?bvp,
                           ?addrs1, ?addrs2, vk1, vk2, ?rof,
                           length(vals), vals) &*&
           true == no_such_keys(v, vals, vk1, vk2);
  ensures valsp<t1,t2,vt>(values, vsz, fvp, bvp,
                          map_erase_fp(addrs1, vk1(v)),
                          map_erase_fp(addrs2, vk2(v)),
                          vk1, vk2, rof,
                          length(vals), vals);
  {
    open valsp(values, vsz, fvp, bvp, addrs1, addrs2, vk1, vk2, rof,
               length(vals), vals);
    switch(vals) {
      case nil:
        break;
      case cons(h,t):
        erase_addrs(values + vsz, t, v, vk1, vk2);
        switch(h) {
          case none: break;
          case some(x):
            map_erase_has_unrelevant(addrs1, vk1(v), vk1(x));
            map_erase_has_unrelevant(addrs2, vk2(v), vk2(x));
            map_erase_get_unrelevant(addrs1, vk1(v), vk1(x));
            map_erase_get_unrelevant(addrs2, vk2(v), vk2(x));
        }
    }
    close valsp(values, vsz, fvp, bvp,
                map_erase_fp(addrs1, vk1(v)),
                map_erase_fp(addrs2, vk2(v)),
                vk1, vk2, rof,
                length(vals), vals);
  }
  @*/

/*@
  lemma void no_such_keys_back<t1,t2,vt>(list<option<vt> > vals,
                                         vt v1, vt v2,
                                         fixpoint (vt,t1) vk1,
                                         fixpoint (vt,t2) vk2)
  requires true == no_such_keys(v1, vals, vk1, vk2) &*&
           true == mem(some(v2), vals);
  ensures vk1(v1) != vk1(v2) &*& vk2(v1) != vk2(v2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none: no_such_keys_back(t, v1, v2, vk1, vk2);
          case some(x):
            if (x == v2) return;
            else no_such_keys_back(t, v1, v2, vk1, vk2);
        }
    }
  }
  @*/

/*@
  lemma void all_keys_differ_no_such_keys<t1,t2,vt>(list<option<vt> > vals,
                                                    int index,
                                                    fixpoint (vt,t1) vk1,
                                                    fixpoint (vt,t2) vk2)
  requires true == all_keys_differ(vals, vk1, vk2) &*&
           0 <= index &*& index < length(vals) &*&
           nth(index, vals) == some(?v);
  ensures true == no_such_keys(v, update(index, none, vals), vk1, vk2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none: all_keys_differ_no_such_keys(t, index-1, vk1, vk2);
          case some(x):
            if (index == 0) {
            } else {
              all_keys_differ_no_such_keys(t, index-1, vk1, vk2);
              update_tail_tail_update(h, t, index, none);
              assert true == mem(some(v), t);
              no_such_keys_back(t, x, v, vk1, vk2);
            }
        }
    }
  }
  @*/

/*@
  lemma void no_such_keys_these_differ<t1,t2,vt>(list<option<vt> > vals,
                                                 int index,
                                                 vt v,
                                                 fixpoint (vt,t1) vk1,
                                                 fixpoint (vt,t2) vk2)
  requires true == no_such_keys(v, vals, vk1, vk2) &*&
           0 <= index &*& index < length(vals) &*&
           nth(index, vals) == some(?x);
  ensures vk1(v) != vk1(x) &*& vk2(v) != vk2(x);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none: no_such_keys_these_differ(t, index-1, v, vk1, vk2);
          case some(a):
            if (index != 0) no_such_keys_these_differ(t, index-1, v, vk1, vk2);
        }
    }
  }

  lemma void all_keys_differ_these_differ<t1,t2,vt>(list<option<vt> > vals,
                                                    int i, int j,
                                                    fixpoint (vt,t1) vk1,
                                                    fixpoint (vt,t2) vk2)
  requires true == all_keys_differ(vals, vk1, vk2) &*&
           0 <= i &*& i < j &*& j < length(vals) &*&
           nth(i, vals) == some(?a) &*&
           nth(j, vals) == some(?b);
  ensures vk1(a) != vk1(b) &*& vk2(a) != vk2(b);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            all_keys_differ_these_differ(t, i-1, j-1, vk1, vk2);
            break;
          case some(v):
            if (i == 0) {
              assert v == a;
              no_such_keys_these_differ(t, j-1, v, vk1, vk2);
            } else {
              all_keys_differ_these_differ(t, i-1, j-1, vk1, vk2);
            }
        }
    }
  }
  @*/

/*@
  lemma void map_has_erase_size_dec<kt,vt>(list<pair<kt,vt> > m,
                                            kt k)
  requires true == map_has_fp(m, k);
  ensures map_size_fp(m) == map_size_fp(map_erase_fp(m, k)) + 1;
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != k)
          map_has_erase_size_dec(t, k);
    }
  }
  @*/


/*@
  lemma void map_erase_erase_swap<kt,vt>(list<pair<kt,vt> > m, kt k1, kt k2)
  requires true;
  ensures map_erase_fp(map_erase_fp(m, k1), k2) ==
          map_erase_fp(map_erase_fp(m, k2), k1);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != k2) {
          map_erase_erase_swap(t, k1, k2);
        }
    }
  }
  @*/

/*@

  lemma void erase_one_insync<t1,t2,vt>(list<option<vt> > vals,
                                        list<pair<t1,int> > m1,
                                        list<pair<t2,int> > m2,
                                        int index,
                                        vt v,
                                        fixpoint (vt,t1) vk1,
                                        fixpoint (vt,t2) vk2,
                                        int capacity)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals)) &*&
           0 <= index &*& index < length(vals) &*&
           nth(index, vals) == some(v) &*&
           true == all_keys_differ(vals, vk1, vk2);
  ensures true == insync_fp(update(index, none, vals),
                            map_erase_fp(m1, vk1(v)),
                            map_erase_fp(m2, vk2(v)),
                            vk1, vk2, capacity - length(vals));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            assert index != 0;
            erase_one_insync(t, m1, m2, index-1, v, vk1, vk2, capacity);
            break;
          case some(x):
            if (index == 0) {
              assert x == v;
            } else {
              erase_one_insync(t, map_erase_fp(m1, vk1(x)),
                               map_erase_fp(m2, vk2(x)),
                               index-1, v,
                               vk1, vk2, capacity);
              map_erase_erase_swap(m1, vk1(x), vk1(v));
              map_erase_erase_swap(m2, vk2(x), vk2(v));
              update_tail_tail_update(h, t, index, none);
              all_keys_differ_these_differ(vals, 0, index, vk1, vk2);
              map_erase_has_unrelevant(m1, vk1(v), vk1(x));
              map_erase_has_unrelevant(m2, vk2(v), vk2(x));
              map_erase_get_unrelevant(m1, vk1(v), vk1(x));
              map_erase_get_unrelevant(m2, vk2(v), vk2(x));
            }
        }
    }
  }
  @*/

/*@
  lemma void erase_unrelevant_no_extra_ptrs<t>(list<pair<t, void*> > addrs,
                                               list<pair<t, int> > m,
                                               t k)
  requires true == no_extra_ptrs(addrs, m) &*&
           false == map_has_fp(addrs, k);
  ensures true == no_extra_ptrs(addrs, map_erase_fp(m, k));
  {
    switch(addrs) {
      case nil: return;
      case cons(h,t):
        assert fst(h) != k;
        erase_unrelevant_no_extra_ptrs(t, m, k);
        map_erase_has_unrelevant(m, k, fst(h));
    }
  }
  @*/

/*@
  lemma void erase_one_no_extra_ptrs<t>(list<pair<t, void*> > addrs,
                                        list<pair<t, int> > m,
                                        t k)
  requires true == no_extra_ptrs(addrs, m);
  ensures true == no_extra_ptrs(map_erase_fp(addrs, k), map_erase_fp(m, k));
  {
    switch(addrs) {
      case nil: return;
      case cons(h,t):
        if (fst(h) == k) {
          erase_unrelevant_no_extra_ptrs(t, m, k);
        } else {
          erase_one_no_extra_ptrs(t, m, k);
          map_erase_has_unrelevant(m, k, fst(h));
          map_erase_has_unrelevant(t, k, fst(h));
        }
    }
  }
  @*/

/*@
  lemma void erase_one_no_such_keys<t1,t2,vt>(list<option<vt> > vals,
                                              vt v,
                                              int index,
                                              fixpoint (vt,t1) vk1,
                                              fixpoint (vt,t2) vk2)
  requires true == no_such_keys(v, vals, vk1, vk2) &*&
           0 <= index &*& index < length(vals);
  ensures true == no_such_keys(v, update(index, none, vals), vk1, vk2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (index != 0) {
          erase_one_no_such_keys(t, v, index-1, vk1, vk2);
          update_tail_tail_update(h, t, index, none);
          switch(h) {
            case none: break;
            case some(x): break;
          }
        }
    }
  }

  lemma void erase_one_all_keys_differ<t1,t2,vt>(list<option<vt> > vals,
                                                 int index,
                                                 fixpoint (vt,t1) vk1,
                                                 fixpoint (vt,t2) vk2)
  requires true == all_keys_differ(vals, vk1, vk2) &*&
           0 <= index &*& index < length(vals);
  ensures true == all_keys_differ(update(index, none, vals), vk1, vk2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (index == 0) {
        } else {
          erase_one_all_keys_differ(t, index-1, vk1, vk2);
          update_tail_tail_update(h, t, index, none);
          switch(h) {
            case none: break;
            case some(v):
              erase_one_no_such_keys(t, v, index-1, vk1, vk2);
          };
        }
    }
  }
  @*/

/*@
  lemma void insync_has<t1,t2,vt>(list<option<vt> > vals,
                                  list<pair<t1, int> > m1,
                                  list<pair<t2, int> > m2,
                                  fixpoint (vt,t1) vk1,
                                  fixpoint (vt,t2) vk2,
                                  int index,
                                  int capacity)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals)) &*&
           0 <= index &*& index < length(vals) &*&
           nth(index, vals) == some(?v);
  ensures true == map_has_fp(m1, vk1(v)) &*&
          true == map_has_fp(m2, vk2(v));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none: insync_has(t, m1, m2, vk1, vk2, index-1, capacity);
          case some(x):
            if (index == 0) {
            } else {
              insync_has(t, map_erase_fp(m1, vk1(x)),
                         map_erase_fp(m2, vk2(x)), vk1, vk2, index-1, capacity);
              if (!map_has_fp(m1, vk1(v)))
                map_erase_has_unrelevant(m1, vk1(x), vk1(v));
              if (!map_has_fp(m2, vk2(v)))
                map_erase_has_unrelevant(m2, vk2(x), vk2(v));
            }
        }
    }
  }
  @*/

int dmap_erase/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             0 <= index &*& index < dmap_cap_fp(m); @*/
/*@ ensures result == 1 &*&
            dmappingp<K1,K2,V>(dmap_erase_fp(m, index, vk1, vk2),
                               kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  //@ void* values = map->values;
  /*@ assert valsp(values, vsz, fvp, bvp,
                   ?addrs1, ?addrs2, vk1, vk2, rof,
                   ?cap, ?vals);
    @*/
  //@ vals_len_is_cap(vals, cap);
  void* key_a = 0;
  void* out_key_a = 0;
  void* key_b = 0;
  void* out_key_b = 0;
  //@ mul_bounds(index, cap, vsz, 4096);
  //@ mul_mono_strict(index, cap, vsz);
  //@ extract_value(map->values, vals, index);
  void* my_value = map->values + index*map->value_size;
  dmap_extract_keys *exk = map->exk;
  exk(my_value, &key_a, &key_b);
  //@ assert [0.5]bvp(my_value, ?v);


  /*@ assert mapping(?m1, addrs1, kp1, rp1, hsh1, ?keys_cap,
                     ?bbs1, ?kps1, ?khs1, ?chns1, ?vals1);
    @*/
  /*@ assert mapping(?m2, addrs2, kp2, rp2, hsh2, keys_cap,
                     ?bbs2, ?kps2, ?khs2, ?chns2, ?vals2);
    @*/
  map_key_hash *hsh_a = map->hsh_a;
  int hash1 = hsh_a(key_a);

  //@ insync_has(vals, m1, m2, vk1, vk2, index, cap);
  map_impl_erase(map->bbs_a, map->kps_a, map->khs_a, map->chns_a, key_a,
                 map->eq_a, hash1,
                 map->keys_capacity, &out_key_a);
  //@ assert [?x1]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x1]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ assert [?x2]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x2]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  map_key_hash *hsh_b = map->hsh_b;
  int hash2 = hsh_b(key_b);
  //@ open [x2]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ open [x1]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  /*@ close hide_mapping(map_erase_fp(m1, vk1(v)),
                         map_erase_fp(addrs1, vk1(v)),
                         kp1, rp1, hsh1, keys_cap,
                         bbs1, kps1, khs1, chns1, vals1);
    @*/
  map_impl_erase(map->bbs_b, map->kps_b, map->khs_b, map->chns_b, key_b,
                 map->eq_b, hash2,
                 map->keys_capacity, &out_key_b);
  /*@ open hide_mapping(_, _, kp1, rp1, hsh1, keys_cap,
                        bbs1, kps1, khs1, chns1, vals1);
    @*/
  //@ assert true == rof(my_value, out_key_a, out_key_b);
  dmap_pack_keys *pk = map->pk;
  pk(my_value, key_a, key_b);
  pk(my_value, out_key_a, out_key_b);
  uq_value_destr* dstr = map->dstr;
  dstr(my_value);
  --map->n_vals;
  //@ take_update_unrelevant(index, index, none, vals);
  //@ drop_update_unrelevant(index+1, index, none, vals);
  //@ nth_update(index, index, none, vals);
  //@ update_values_hole(map->values, update(index, none, vals), index);
  //@ all_keys_differ_no_such_keys(vals, index, vk1, vk2);
  //@ erase_addrs(map->values, update(index, none, vals), v, vk1, vk2);
  //@ map_has_erase_size_dec(m1, vk1(v));
  //@ erase_one_insync(vals, m1, m2, index, v, vk1, vk2, cap);
  //@ erase_one_no_extra_ptrs(addrs1, m1, vk1(v));
  //@ erase_one_no_extra_ptrs(addrs2, m2, vk2(v));
  //@ erase_one_all_keys_differ(vals, index, vk1, vk2);
  /*@ close dmappingp(dmap_erase_fp(m, index, vk1, vk2),
                      kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  return 1;
}

/*@
  lemma void insync_map_size_val_size<t1,t2,vt>(list<option<vt> > vals,
                                                list<pair<t1,int> > m1,
                                                list<pair<t2,int> > m2,
                                                fixpoint (vt,t1) vk1,
                                                fixpoint (vt,t2) vk2,
                                                int capacity)
  requires true == insync_fp(vals, m1, m2, vk1, vk2,
                             capacity - length(vals));
  ensures map_size_fp(m1) ==
          length(nonempty_indexes_fp(vals, capacity - length(vals))) &*&
          map_size_fp(m2) == map_size_fp(m1);
  {
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_map_size_val_size(t, m1, m2, vk1, vk2, capacity);
            return;
          case some(v):
            insync_map_size_val_size(t, map_erase_fp(m1, vk1(v)),
                                     map_erase_fp(m2, vk2(v)),
                                     vk1, vk2, capacity);
            map_has_erase_size_dec(m1, vk1(v));
            map_has_erase_size_dec(m2, vk2(v));
            return;
        }
    }
  }
  @*/

int dmap_size/*@ <K1,K2,V> @*/(struct DoubleMap* map)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, map); @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, map) &*&
            result == dmap_size_fp(m); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
  //@ assert m == dmap(?ma, ?mb, ?val_arr);
  //@ insync_map_size_val_size(val_arr, ma, mb, vk1, vk2, length(val_arr));
  //@ assert map_size_fp(ma) == dmap_size_fp(m);
  return map->n_vals;
  /*@ close dmappingp(m,
                      kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, map); @*/
}

/*@
  lemma void dmap_erase_erase_swap<t1,t2,vt>(dmap<t1,t2,vt> m,
                                             int i1, int i2,
                                             fixpoint (vt,t1) vk1,
                                             fixpoint (vt,t2) vk2)
  requires true;
  ensures dmap_erase_fp(dmap_erase_fp(m, i1, vk1, vk2), i2, vk1, vk2) ==
          dmap_erase_fp(dmap_erase_fp(m, i2, vk1, vk2), i1, vk1, vk2);
  {
    switch(m) { case dmap(ma, mb, val_arr):
      if (i1 == i2) {
        return;
      } else {
        map_erase_erase_swap(ma, vk1(get_some(nth(i1, val_arr))),
                                 vk1(get_some(nth(i2, val_arr))));
        map_erase_erase_swap(mb, vk2(get_some(nth(i1, val_arr))),
                                 vk2(get_some(nth(i2, val_arr))));
        nth_update_unrelevant(i1, i2, none, val_arr);
        nth_update_unrelevant(i2, i1, none, val_arr);
        update_update(val_arr, i1, none, i2, none);
      }
    }
  }
  @*/

/*@
  lemma void dmap_erase_another_one<t1,t2,vt>(dmap<t1,t2,vt> m,
                                              list<int> idxs,
                                              int idx,
                                              fixpoint (vt,t1) vk1,
                                              fixpoint (vt,t2) vk2)
  requires true;
  ensures dmap_erase_fp(dmap_erase_all_fp(m, idxs, vk1, vk2), idx, vk1, vk2) ==
          dmap_erase_all_fp(m, append(idxs, cons(idx, nil)), vk1, vk2);
  {
    switch(idxs) {
      case nil: return;
      case cons(h,t):
        dmap_erase_another_one(m, t, idx, vk1, vk2);
        dmap_erase_erase_swap(dmap_erase_all_fp(m, t, vk1, vk2),
                              idx, h, vk1, vk2);
    }
  }
  @*/

/*@
  lemma void dmap_erase_keeps_cap<t1,t2,vt>(dmap<t1,t2,vt> m,
                                            int idx,
                                            fixpoint (vt,t1) vk1,
                                            fixpoint (vt,t2) vk2)
  requires true;
  ensures dmap_cap_fp(m) == dmap_cap_fp(dmap_erase_fp(m, idx, vk1, vk2));
  {
    switch(m) { case dmap(m1, m2, vals):
    }
  }
  @*/

/*@
  lemma void dmap_erase_other_keeps_used<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                   int idx1, int idx2,
                                                   fixpoint (vt,t1) vk1,
                                                   fixpoint (vt,t2) vk2)
  requires idx1 != idx2;
  ensures dmap_index_used_fp(dmap_erase_fp(m, idx1, vk1, vk2), idx2) ==
          dmap_index_used_fp(m, idx2);
  {
    switch(m) { case dmap(m1,m2,vals):
      nth_update_unrelevant(idx2, idx1, none, vals);
    }
  }
  @*/

/*@
  lemma void dmap_erase_keeps_rest<t1,t2,vt>(dmap<t1,t2,vt> m,
                                             int idx,
                                             list<int> ids,
                                             fixpoint (vt,t1) vk1,
                                             fixpoint (vt,t2) vk2)
  requires true == forall(ids, (dmap_index_used_fp)(m)) &*&
           false == mem(idx, remove(idx, ids));
  ensures true == forall(remove(idx, ids),
                         (dmap_index_used_fp)(dmap_erase_fp(m, idx, vk1, vk2)));
  {
    switch(ids){
      case nil: return;
      case cons(h,t):
        if (h != idx) {
          dmap_erase_keeps_rest(m, idx, t, vk1, vk2);
          dmap_erase_other_keeps_used(m, idx, h, vk1, vk2);
        } else {
          if (mem(idx, remove(idx, t))) mem_remove_mem(idx, idx, t);
          dmap_erase_keeps_rest(m, idx, t, vk1, vk2);
          remove_nonmem(idx, t);
        }
    }
  }
  @*/

/*@
  lemma void empty_vals_len<vt>(nat len)
  requires true;
  ensures length(empty_vals_fp<vt>(len)) == int_of_nat(len);
  {
    switch(len) {
      case zero: return;
      case succ(n): empty_vals_len(n);
    }
  }
  @*/

/*@
  lemma void empty_dmap_cap<t1,t2,vt>(int len)
  requires 0 <= len;
  ensures dmap_cap_fp(empty_dmap_fp<t1,t2,vt>(len)) == len;
  {
    empty_vals_len(nat_of_int(len));
  }
  @*/

/*@
  lemma void dmap_empty_no_indexes_used_impl<vt>(nat len, int start)
  requires true;
  ensures nonempty_indexes_fp(empty_vals_fp(len), start) == nil;
  {
    switch(len) {
      case zero: return;
      case succ(n):
        dmap_empty_no_indexes_used_impl(n, start+1);
    }
  }

  lemma void dmap_empty_no_indexes_used<t1,t2,vt>(int len)
  requires 0 <= len;
  ensures dmap_indexes_used_fp(empty_dmap_fp<t1,t2,vt>(len)) == nil;
  {
    dmap_empty_no_indexes_used_impl(nat_of_int(len), 0);
  }
  @*/

/*@
  lemma void dmap_indexes_used_above_start<vt>(list<option<vt> > vals,
                                               int x, int start)
  requires x < start;
  ensures false == mem(x, nonempty_indexes_fp(vals, start));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        dmap_indexes_used_above_start(t, x, start+1);
        switch(h) {
          case none: break;
          case some(y): break;
        }
    }
  }

  @*/

/*@
  lemma void nonmem_remove<t>(t x, list<t> l)
  requires false == mem(x, l);
  ensures l == remove(x, l);
  {
    switch(l) {
      case nil: return;
      case cons(h,t):
        nonmem_remove(x, t);
    }
  }
  @*/

/*@
  lemma void dmap_erase_removes_index_impl<vt>(list<option<vt> > vals,
                                               int idx, int start)
  requires start <= idx;
  ensures nonempty_indexes_fp(update(idx-start, none, vals), start) ==
          remove(idx, nonempty_indexes_fp(vals, start));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            if (start == idx) {
              dmap_indexes_used_above_start(t, idx, start+1);
              nonmem_remove(idx, nonempty_indexes_fp(vals, start));
            } else {
              dmap_erase_removes_index_impl(t, idx, start+1);
            }
            break;
          case some(x):
            if (start != idx) {
              dmap_erase_removes_index_impl(t, idx, start+1);
            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_erase_removes_index<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                int idx,
                                                fixpoint (vt,t1) vk1,
                                                fixpoint (vt,t2) vk2)
  requires 0 <= idx;
  ensures dmap_indexes_used_fp(dmap_erase_fp(m, idx, vk1, vk2)) ==
          remove(idx, dmap_indexes_used_fp(m));
  {
    switch(m) { case dmap(ma, mb, vals):
      dmap_erase_removes_index_impl(vals, idx, 0);
    }
  }
  @*/

/*@
  lemma void dmap_indexes_used_distinct_impl<vt>(list<option<vt> > vals,
                                                 int start)
  requires true;
  ensures true == distinct(nonempty_indexes_fp(vals, start));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        dmap_indexes_used_distinct_impl(t, start+1);
        dmap_indexes_used_above_start(t, start, start+1);
        assert true == distinct(nonempty_indexes_fp(t, start+1));
        switch(h) {
          case none: break;
          case some(x): break;
        }
    }
  }
  @*/

/*@
  lemma void dmap_indexes_used_distinct<t1,t2,vt>(dmap<t1,t2,vt> m)
  requires true;
  ensures true == distinct(dmap_indexes_used_fp(m));
  {
    switch(m) { case dmap(ma, mb, vals):
      dmap_indexes_used_distinct_impl(vals, 0);
    }
  }
  @*/

/*@
  lemma void dmap_indexes_contain_index_used_impl<vt>(list<option<vt> > vals,
                                                      int idx, int start)
  requires 0 <= start &*& start <= idx &*& idx-start < length(vals);
  ensures mem(idx, nonempty_indexes_fp(vals, start)) ==
          (nth(idx-start, vals) != none);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (start == idx) {
          switch(h) {
            case none:
              dmap_indexes_used_above_start(t, start, start+1);
              break;
            case some(x): break;
          }
        } else {
          dmap_indexes_contain_index_used_impl(t, idx, start+1);
          switch(h) {
            case none: break;
            case some(x): break;
          }
        }
    }
  }
  @*/

/*@
  lemma void dmap_indexes_contain_index_used<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                       int idx)
  requires 0 <= idx &*& idx < dmap_cap_fp(m);
  ensures mem(idx, dmap_indexes_used_fp(m)) == dmap_index_used_fp(m, idx);
  {
    switch(m) { case dmap(ma, mb, vals):
      dmap_indexes_contain_index_used_impl(vals, idx, 0);
    }
  }
  @*/

/*@
  lemma void dmap_index_used_inbounds<t1,t2,vt>(dmap<t1,t2,vt> m, int idx)
  requires true == dmap_index_used_fp(m, idx);
  ensures 0 <= idx &*& idx < dmap_cap_fp(m);
  {
    switch(m) { case dmap(ma, mb, vals) :
    }
  }
  @*/

/*@
  lemma void dmap_size_of_indexes_used<t1,t2,vt>(dmap<t1,t2,vt> m)
  requires true;
  ensures dmap_size_fp(m) == length(dmap_indexes_used_fp(m));
  {
  }
  @*/

/*@
  lemma void insync_get_inbounds1<t1,t2,vt>(list<option<vt> > vals,
                                            list<pair<t1,int> > m1,
                                            list<pair<t2,int> > m2,
                                            fixpoint (vt,t1) vk1,
                                            fixpoint (vt,t2) vk2,
                                            int start_index,
                                            t1 k1)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == map_has_fp(m1, k1);
  ensures start_index <= map_get_fp(m1, k1) &*&
          map_get_fp(m1, k1) < start_index + length(vals) &*&
          nth(map_get_fp(m1, k1) - start_index, vals) != none;
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_get_inbounds1(t, m1, m2, vk1, vk2,
                                 start_index+1, k1);
            break;
          case some(v):
            if (vk1(v) != k1) {
              map_erase_has_unrelevant(m1, vk1(v), k1);
              insync_get_inbounds1(t, map_erase_fp(m1, vk1(v)),
                                   map_erase_fp(m2, vk2(v)),
                                   vk1, vk2, start_index+1,
                                   k1);
              map_erase_get_unrelevant(m1, vk1(v), k1);
            }
            break;
        }
    }
  }
  @*/

/*@
  lemma void insync_get_inbounds2<t1,t2,vt>(list<option<vt> > vals,
                                            list<pair<t1,int> > m1,
                                            list<pair<t2,int> > m2,
                                            fixpoint (vt,t1) vk1,
                                            fixpoint (vt,t2) vk2,
                                            int start_index,
                                            t2 k2)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == map_has_fp(m2, k2);
  ensures start_index <= map_get_fp(m2, k2) &*&
          map_get_fp(m2, k2) < start_index + length(vals) &*&
          nth(map_get_fp(m2, k2) - start_index, vals) != none;
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_get_inbounds2(t, m1, m2, vk1, vk2,
                                 start_index+1, k2);
            break;
          case some(v):
            if (vk2(v) != k2) {
              map_erase_has_unrelevant(m2, vk2(v), k2);
              insync_get_inbounds2(t, map_erase_fp(m1, vk1(v)),
                                   map_erase_fp(m2, vk2(v)),
                                   vk1, vk2, start_index+1,
                                   k2);
              map_erase_get_unrelevant(m2, vk2(v), k2);
            }
            break;
        }
    }
  }
  @*/

/*@

  lemma void dmap_get_k1_limits<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1)
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           dmap_has_k1_fp<t1,t2,vt>(m, k1) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2, fvp,
                              bvp, rof, vsz, vk1, vk2, recp1, recp2, mp) &*&
          0 <= dmap_get_k1_fp<t1,t2,vt>(m, k1) &*&
          dmap_get_k1_fp<t1,t2,vt>(m, k1) < dmap_cap_fp(m) &*&
          true == dmap_index_used_fp(m, dmap_get_k1_fp(m, k1));
  {
    open dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                   vsz, vk1, vk2, recp1, recp2, mp);
    switch(m) { case dmap(ma, mb, vals):
      insync_get_inbounds1(vals, ma, mb, vk1, vk2, 0, k1);
    }
    close dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                    vsz, vk1, vk2, recp1, recp2, mp);
  }

  @*/
/*@

  lemma void dmap_get_k2_limits<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2)
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           dmap_has_k2_fp<t1,t2,vt>(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, mp) &*&
          0 <= dmap_get_k2_fp<t1,t2,vt>(m, k2) &*&
          dmap_get_k2_fp<t1,t2,vt>(m, k2) < dmap_cap_fp(m) &*&
          true == dmap_index_used_fp(m, dmap_get_k2_fp(m, k2));
  {
    open dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                   vsz, vk1, vk2, recp1, recp2, mp);
    switch(m) { case dmap(ma, mb, vals):
      insync_get_inbounds2(vals, ma, mb, vk1, vk2, 0, k2);
    }
    close dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                    vsz, vk1, vk2, recp1, recp2, mp);
  }

  @*/

/*@
  lemma void dmap_erase_all_has_trans<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                t1 k1, list<int> ids,
                                                fixpoint (vt,t1) vk1,
                                                fixpoint (vt,t2) vk2)
  requires false == dmap_has_k1_fp(m, k1);
  ensures false == dmap_has_k1_fp(dmap_erase_all_fp(m, ids, vk1, vk2), k1);
  {
    switch(ids) {
      case nil: return;
      case cons(h,t):
        dmap_erase_all_has_trans(m, k1, t, vk1, vk2);
        switch(dmap_erase_all_fp(m, t, vk1, vk2)) { case dmap(ma, mb, vals):
          map_erase_preserves_not_has(ma, vk1(get_some(nth(h, vals))), k1);
        }
    }
  }
  @*/

/*@
  lemma void insync_index_consistent<t1,t2,vt>(list<option<vt> > vals,
                                               list<pair<t1,int> > m1,
                                               list<pair<t2,int> > m2,
                                               fixpoint (vt,t1) vk1,
                                               fixpoint (vt,t2) vk2,
                                               int ind,
                                               int start_index)
  requires start_index <= ind &*& ind - start_index < length(vals) &*&
           nth(ind - start_index, vals) == some(?v) &*&
           true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == all_keys_differ(vals, vk1, vk2);
  ensures map_get_fp(m1, vk1(v)) == ind &*&
          true == map_has_fp(m1, vk1(v)) &*&
          map_get_fp(m2, vk2(v)) == ind &*&
          true == map_has_fp(m2, vk2(v));
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_index_consistent(t, m1, m2, vk1, vk2, ind, start_index+1);
            break;
          case some(x):
            if (start_index < ind) {
              insync_index_consistent(t, map_erase_fp(m1, vk1(x)),
                                      map_erase_fp(m2, vk2(x)),
                                      vk1, vk2, ind, start_index+1);
              all_keys_differ_these_differ(vals, 0, ind - start_index,
                                           vk1, vk2);
              map_erase_has_unrelevant(m1, vk1(x), vk1(v));
              map_erase_has_unrelevant(m2, vk2(x), vk2(v));
              map_erase_get_unrelevant(m1, vk1(x), vk1(v));
              map_erase_get_unrelevant(m2, vk2(x), vk2(v));
            } else {
            }
        }
    }
  }
  @*/

/*@
  lemma void insync_mappings_keep_recps<t1,t2,vt>(list<option<vt> > vals,
                                                  list<pair<t1,int> > m1,
                                                  list<pair<t2,int> > m2,
                                                  fixpoint (vt,t1) vk1,
                                                  fixpoint (vt,t2) vk2,
                                                  int ind)
  requires 0 <= ind &*& ind < length(vals) &*&
           nth(ind, vals) == some(?v) &*&
           true == insync_fp(vals, m1, m2, vk1, vk2, 0) &*&
           true == all_keys_differ(vals, vk1, vk2) &*&
           mapping(m1, ?addrs1, ?kp1, ?rp1, ?hsh1,
                   ?cap1, ?bbs1, ?kps1, ?khs1, ?chns1, ?vals1) &*&
           mapping(m2, ?addrs2, ?kp2, ?rp2, ?hsh2,
                   ?cap2, ?bbs2, ?kps2, ?khs2, ?chns2, ?vals2);
  ensures true == rp1(vk1(v), ind) &*& true == rp2(vk2(v), ind) &*&
          mapping(m1, addrs1, kp1, rp1, hsh1,
                  cap1, bbs1, kps1, khs1, chns1, vals1) &*&
          mapping(m2, addrs2, kp2, rp2, hsh2,
                  cap2, bbs2, kps2, khs2, chns2, vals2);
  {
    insync_index_consistent(vals, m1, m2, vk1, vk2, ind, 0);
    map_get_keeps_recp(m1, vk1(v));
    map_get_keeps_recp(m2, vk2(v));
  }
  @*/

/*@
  lemma void dmap_get_by_index_rp<t1,t2,vt>(dmap<t1,t2,vt> m, int idx)
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           dmap_index_used_fp(m, idx) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, mp) &*&
          true == recp1(vk1(dmap_get_val_fp(m, idx)),
                        idx) &*&
          true == recp2(vk2(dmap_get_val_fp(m, idx)),
                        idx);
  {
    open dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                   vsz, vk1, vk2, recp1, recp2, mp);
    switch(m) { case dmap(ma, mb, vals):
      insync_mappings_keep_recps(vals, ma, mb, vk1, vk2, idx);
    }
    close dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                    vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void insync_get_above_start1<t1,t2,vt>(list<option<vt> > vals,
                                               list<pair<t1,int> > m1,
                                               list<pair<t2,int> > m2,
                                               fixpoint (vt,t1) vk1,
                                               fixpoint (vt,t2) vk2,
                                               t1 k1,
                                               int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == map_has_fp(m1, k1);
  ensures start_index <= map_get_fp(m1, k1);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_get_above_start1(t, m1, m2, vk1, vk2, k1, start_index+1);
          case some(v):
            if (vk1(v) == k1) {
              assert map_get_fp(m1, k1) == start_index;
            } else {
              map_erase_has_unrelevant(m1, vk1(v), k1);
              insync_get_above_start1(t, map_erase_fp(m1, vk1(v)),
                                      map_erase_fp(m2, vk2(v)),
                                      vk1, vk2, k1, start_index+1);
              map_erase_get_unrelevant(m1, vk1(v), k1);
            }
        }
    }
  }
@*/

/*@
  lemma void insync_get_by_k1_invertible<t1,t2,vt>(list<option<vt> > vals,
                                                   list<pair<t1,int> > m1,
                                                   list<pair<t2,int> > m2,
                                                   fixpoint (vt,t1) vk1,
                                                   fixpoint (vt,t2) vk2,
                                                   t1 k1,
                                                   int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == all_keys_differ(vals, vk1, vk2) &*&
           true == map_has_fp(m1, k1);
  ensures start_index <= map_get_fp(m1, k1) &*&
          map_get_fp(m1, k1) - start_index < length(vals) &*&
          nth(map_get_fp(m1, k1) - start_index, vals) == some(?x) &*&
          k1 == vk1(x);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_get_by_k1_invertible(t, m1, m2, vk1, vk2, k1,
                                        start_index+1);
            insync_get_above_start1(t, m1, m2, vk1, vk2, k1, start_index+1);
            return;
          case some(v):
            if (vk1(v) == k1) {
              assert map_get_fp(m1, k1) == start_index;
            } else {
              map_erase_has_unrelevant(m1, vk1(v), k1);
              insync_get_by_k1_invertible(t, map_erase_fp(m1, vk1(v)),
                                          map_erase_fp(m2, vk2(v)),
                                          vk1, vk2, k1, start_index+1);
              insync_get_above_start1(t, map_erase_fp(m1, vk1(v)),
                                      map_erase_fp(m2, vk2(v)),
                                      vk1, vk2, k1, start_index+1);
              map_erase_get_unrelevant(m1, vk1(v), k1);
            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_get_by_k1_invertible<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k1)
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           dmap_has_k1_fp(m, k1) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, mp) &*&
          true == dmap_index_used_fp(m, dmap_get_k1_fp(m, k1)) &*&
          k1 == vk1(dmap_get_val_fp(m, dmap_get_k1_fp(m, k1)));
  {
    open dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                   vsz, vk1, vk2, recp1, recp2, mp);
    switch(m) { case dmap(ma, mb, vals):
      insync_get_by_k1_invertible(vals, ma, mb, vk1, vk2, k1, 0);
    }
    close dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                    vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void insync_get_above_start2<t1,t2,vt>(list<option<vt> > vals,
                                               list<pair<t1,int> > m1,
                                               list<pair<t2,int> > m2,
                                               fixpoint (vt,t1) vk1,
                                               fixpoint (vt,t2) vk2,
                                               t2 k2,
                                               int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == map_has_fp(m2, k2);
  ensures start_index <= map_get_fp(m2, k2);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_get_above_start2(t, m1, m2, vk1, vk2, k2, start_index+1);
          case some(v):
            if (vk2(v) == k2) {
              assert map_get_fp(m2, k2) == start_index;
            } else {
              map_erase_has_unrelevant(m2, vk2(v), k2);
              insync_get_above_start2(t, map_erase_fp(m1, vk1(v)),
                                      map_erase_fp(m2, vk2(v)),
                                      vk1, vk2, k2, start_index+1);
              map_erase_get_unrelevant(m2, vk2(v), k2);
            }
        }
    }
  }
@*/

/*@
  lemma void insync_get_by_k2_invertible<t1,t2,vt>(list<option<vt> > vals,
                                                   list<pair<t1,int> > m1,
                                                   list<pair<t2,int> > m2,
                                                   fixpoint (vt,t1) vk1,
                                                   fixpoint (vt,t2) vk2,
                                                   t2 k2,
                                                   int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           true == all_keys_differ(vals, vk1, vk2) &*&
           true == map_has_fp(m2, k2);
  ensures start_index <= map_get_fp(m2, k2) &*&
          map_get_fp(m2, k2) - start_index < length(vals) &*&
          nth(map_get_fp(m2, k2) - start_index, vals) == some(?x) &*&
          k2 == vk2(x);
  {
    switch(vals) {
      case nil: return;
      case cons(h,t):
        switch(h) {
          case none:
            insync_get_by_k2_invertible(t, m1, m2, vk1, vk2, k2,
                                        start_index+1);
            insync_get_above_start2(t, m1, m2, vk1, vk2, k2, start_index+1);
            return;
          case some(v):
            if (vk2(v) == k2) {
              assert map_get_fp(m2, k2) == start_index;
            } else {
              map_erase_has_unrelevant(m2, vk2(v), k2);
              insync_get_by_k2_invertible(t, map_erase_fp(m1, vk1(v)),
                                          map_erase_fp(m2, vk2(v)),
                                          vk1, vk2, k2, start_index+1);
              insync_get_above_start2(t, map_erase_fp(m1, vk1(v)),
                                      map_erase_fp(m2, vk2(v)),
                                      vk1, vk2, k2, start_index+1);
              map_erase_get_unrelevant(m2, vk2(v), k2);
            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_get_by_k2_invertible<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k2)
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           dmap_has_k2_fp(m, k2) == true;
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, mp) &*&
          true == dmap_index_used_fp(m, dmap_get_k2_fp(m, k2)) &*&
          k2 == vk2(dmap_get_val_fp(m, dmap_get_k2_fp(m, k2)));
  {
    open dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                   vsz, vk1, vk2, recp1, recp2, mp);
    switch(m) { case dmap(ma, mb, vals):
      insync_get_by_k2_invertible(vals, ma, mb, vk1, vk2, k2, 0);
    }
    close dmappingp(m, kp1, kp2, hsh1, hsh2, fvp, bvp, rof,
                    vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@

  lemma void dmap_put_get<t1,t2,vt>(dmap<t1,t2,vt> m, int index, vt v,
                                    fixpoint (vt,t1) vk1,
                                    fixpoint (vt,t2) vk2)
  requires 0 <= index &*& index < dmap_cap_fp(m);
  ensures dmap_index_used_fp(dmap_put_fp(m, index, v, vk1, vk2), index) == true &*&
          v == dmap_get_val_fp(dmap_put_fp(m, index, v, vk1, vk2), index);
  {
    switch(m) { case dmap(ma, mb, vals):
    }
  }

  lemma void dmap_get_k1_get_val<t1,t2,vt>(dmap<t1,t2,vt> m, t1 k)
  requires dmappingp<t1,t2,vt>(m,
                               ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           true == dmap_has_k1_fp(m, k);
  ensures dmappingp<t1,t2,vt>(m,
                              kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, mp) &*&
          vk1(dmap_get_val_fp(m, dmap_get_k1_fp(m, k))) == k &*&
          true == recp2(vk2(dmap_get_val_fp(m, dmap_get_k1_fp(m, k))), dmap_get_k1_fp(m,k)) &*&
          true == recp1(k, dmap_get_k1_fp(m,k));
  {
    dmap_get_by_k1_invertible(m, k);
    dmap_get_by_index_rp(m, dmap_get_k1_fp(m, k));
  }

  lemma void dmap_get_k2_get_val<t1,t2,vt>(dmap<t1,t2,vt> m, t2 k)
  requires dmappingp<t1,t2,vt>(m,
                               ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           true == dmap_has_k2_fp(m, k);
  ensures dmappingp<t1,t2,vt>(m,
                              kp1, kp2, hsh1, hsh2,
                              fvp, bvp, rof, vsz,
                              vk1, vk2, recp1, recp2, mp) &*&
          vk2(dmap_get_val_fp(m, dmap_get_k2_fp(m, k))) == k &*&
          true == recp1(vk1(dmap_get_val_fp(m, dmap_get_k2_fp(m, k))), dmap_get_k2_fp(m,k)) &*&
          true == recp2(k, dmap_get_k2_fp(m,k));
  {
    dmap_get_by_k2_invertible(m, k);
    dmap_get_by_index_rp(m, dmap_get_k2_fp(m, k));
  }
  @*/

/*@
  lemma void dmap_erase_all_preserves_cap<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                    list<int> idxs,
                                                    fixpoint (vt,t1) vk1,
                                                    fixpoint (vt,t2) vk2)
  requires true;
  ensures dmap_cap_fp(dmap_erase_all_fp(m, idxs, vk1, vk2)) == dmap_cap_fp(m);
  {
    switch(idxs) {
      case nil: return;
      case cons(h,t):
        dmap_erase_all_preserves_cap(m, t, vk1, vk2);
        dmap_erase_keeps_cap(dmap_erase_all_fp(m, t, vk1, vk2), h, vk1, vk2);
    }
  }
  @*/

/*@
  lemma void dmap_put_preserves_cap<t1,t2,vt>(dmap<t1,t2,vt> m,
                                              int index,
                                              vt v,
                                              fixpoint (vt,t1) vk1,
                                              fixpoint (vt,t2) vk2)
  requires true;
  ensures dmap_cap_fp(dmap_put_fp(m, index, v, vk1, vk2)) == dmap_cap_fp(m);
  {
    switch(m) { case dmap(ma, mb, vals):
    }
  }
  @*/

/*@
  lemma void ge_prev(list<int> l, int x)
  requires true == forall(l, (ge)(x+1));
  ensures true == forall(l, (ge)(x));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        ge_prev(t, x);
    }
  }
  @*/


/*@
  lemma void less_than_boundary_nonmem(list<int> l, int i, int x)
  requires true == forall(l, (ge)(i)) &*& x < i;
  ensures false == mem(x, l);
  {
    switch(l) {
      case nil:
      case cons(h,t):
        less_than_boundary_nonmem(t, i, x);
    }
  }
  @*/

/*@
  lemma void unremove_small_still_no_dups(list<int> l, int i, int x)
  requires true == no_dups(remove(x, l)) &*&
           true == forall(remove(x, l), (ge)(i)) &*&
           x < i;
  ensures true == no_dups(l) &*& true == forall(l, (ge)(x));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        if (h != x) {
          unremove_small_still_no_dups(t, i, x);
          neq_mem_remove(h, x, t);
        } else {
          less_than_boundary_nonmem(t, i, x);
          ge_le_ge(t, i, x);
        }
    }
  }
  @*/


/*@
  lemma void map_erase_removes_index<kt,vt>(list<pair<kt, vt> > m, kt k)
  requires true == map_has_fp(m, k) &*&
           false == mem(map_get_fp(m, k), map(snd, map_erase_fp(m, k)));
  ensures map(snd, map_erase_fp(m, k)) ==
          remove(map_get_fp(m, k), map(snd, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) {
            map_erase_removes_index(t, k);
          }
        }
    }
  }
  @*/


/*@
  lemma void insync_no_dup_indexes_ma_mb<t1,t2,vt>(list<option<vt> > vals,
                                          list<pair<t1, int> > m1,
                                          list<pair<t2, int> > m2,
                                          fixpoint (vt, t1) vk1,
                                          fixpoint (vt, t2) vk2,
                                          int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index);
  ensures true == no_dups(map(snd, m1)) &*&
          true == no_dups(map(snd, m2)) &*&
          true == forall(map(snd, m1), (ge)(start_index)) &*&
          true == forall(map(snd, m2), (ge)(start_index));
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            insync_no_dup_indexes_ma_mb(t, m1, m2, vk1, vk2, start_index + 1);
            ge_prev(map(snd, m1), start_index);
            ge_prev(map(snd, m2), start_index);
          case some(v):
            insync_no_dup_indexes_ma_mb(t, map_erase_fp(m1, vk1(v)),
                                        map_erase_fp(m2, vk2(v)),
                                        vk1, vk2, start_index + 1);
            less_than_boundary_nonmem(map(snd, map_erase_fp(m1, vk1(v))),
                                      start_index + 1, start_index);
            less_than_boundary_nonmem(map(snd, map_erase_fp(m2, vk2(v))),
                                      start_index + 1, start_index);
            map_erase_removes_index(m1, vk1(v));
            map_erase_removes_index(m2, vk2(v));
            unremove_small_still_no_dups(map(snd, m1), start_index + 1,
                                         start_index);
            unremove_small_still_no_dups(map(snd, m2), start_index + 1,
                                         start_index);
        }
    }
  }
  @*/


/*@
  lemma void dmap_indices_no_dups<t1,t2,vt>(list<pair<t1,int> > ma,
                                            list<pair<t2, int> > mb,
                                            list<option<vt> > vals)
  requires dmappingp(dmap(ma, mb, vals), ?kp1, ?kp2, ?hsh1, ?hsh2,
                     ?fvp, ?bvp, ?rof, ?vsz,
                     ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
  ensures dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz,
                    vk1, vk2, recp1, recp2, mp) &*&
          true == no_dups(map(snd, ma)) &*&
          true == no_dups(map(snd, mb));
  {
    open dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                   fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
    insync_no_dup_indexes_ma_mb(vals, ma, mb, vk1, vk2, 0);
    close dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/


/*@
  lemma void snd_contains_unerase<kt>(int i, list<pair<kt, int> > m, kt k)
  requires true == contains(map(snd, map_erase_fp(m, k)), i);
  ensures true == contains(map(snd, m), i);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k && ind != i) {
            snd_contains_unerase(i, t, k);
          }
        }
    }
  }
  @*/


/*@
  lemma void forall_contains_unerase<kt>(list<int> l,
                                         list<pair<kt, int> > m,
                                         kt k)
  requires true == forall(l, (contains)(map(snd, map_erase_fp(m, k))));
  ensures true == forall(l, (contains)(map(snd, m)));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        forall_contains_unerase(t, m, k);
        snd_contains_unerase(h, m, k);
    }
  }
  @*/


/*@
  lemma void map_contains_get<kt>(list<pair<kt, int> > m, kt k)
  requires true == map_has_fp(m, k);
  ensures true == contains(map(snd, m), map_get_fp(m, k));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) {
            map_contains_get(t, k);
          }
        }
    }
  }
  @*/


/*@
lemma void insync_nonemptyindexes_mem_ma_mb<t1,t2,vt>(list<option<vt> > vals,
                                                      list<pair<t1, int> > m1,
                                                      list<pair<t2, int> > m2,
                                                      fixpoint (vt, t1) vk1,
                                                      fixpoint (vt, t2) vk2,
                                                      int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index);
  ensures true == forall(nonempty_indexes_fp(vals, start_index),
                         (contains)(map(snd, m1))) &*&
          true == forall(nonempty_indexes_fp(vals, start_index),
                         (contains)(map(snd, m2)));
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            insync_nonemptyindexes_mem_ma_mb(t, m1, m2, vk1, vk2,
                                             start_index + 1);
          case some(v):
            insync_nonemptyindexes_mem_ma_mb(t, map_erase_fp(m1, vk1(v)),
                                             map_erase_fp(m2, vk2(v)),
                                             vk1, vk2, start_index + 1);
            forall_contains_unerase(nonempty_indexes_fp(t, start_index + 1),
                                    m1, vk1(v));
            forall_contains_unerase(nonempty_indexes_fp(t, start_index + 1),
                                    m2, vk2(v));
            map_contains_get(m1, vk1(v));
            map_contains_get(m2, vk2(v));
        }
    }
  }
  @*/

/*@
  lemma void dmap_indexes_used_used_in_ma_mb<t1,t2,vt>
                (list<pair<t1,int> > ma,
                 list<pair<t2, int> > mb,
                 list<option<vt> > vals)
  requires dmappingp(dmap(ma, mb, vals), ?kp1, ?kp2, ?hsh1, ?hsh2,
                     ?fvp, ?bvp, ?rof, ?vsz,
                     ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
  ensures dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz,
                    vk1, vk2, recp1, recp2, mp) &*&
          true == forall(dmap_indexes_used_fp(dmap(ma, mb, vals)),
                         (contains)(map(snd, ma))) &*&
          true == forall(dmap_indexes_used_fp(dmap(ma, mb, vals)),
                         (contains)(map(snd, mb)));
  {
    open dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                   fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
    insync_nonemptyindexes_mem_ma_mb(vals, ma, mb, vk1, vk2, 0);
    close dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void map_has_the_value<kt,vt>(list<pair<kt, vt> > m, kt k)
  requires true == map_has_fp(m, k);
  ensures true == mem(map_get_fp(m, k), map(snd, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,val):
          if (key != k) map_has_the_value(t, k);
        }
    }
  }
  @*/

/*@
  lemma void insync_nonnone_index_in_ma_mb<t1,t2,vt>(list<option<vt> > vals,
                                                     list<pair<t1, int> > m1,
                                                     list<pair<t2, int> > m2,
                                                     fixpoint (vt, t1) vk1,
                                                     fixpoint (vt, t2) vk2,
                                                     int index,
                                                     int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           0 <= start_index &*&
           start_index <= index &*& index < length(vals) + start_index;
  ensures (mem(index, map(snd, m1)) ==
           (nth(index - start_index, vals) != none)) &*&
          (mem(index, map(snd, m2)) ==
           (nth(index - start_index, vals) != none));
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            if (start_index == index) {
              insync_no_dup_indexes_ma_mb(t, m1, m2, vk1, vk2, start_index + 1);
              less_than_boundary_nonmem(map(snd, m1), start_index + 1, index);
              less_than_boundary_nonmem(map(snd, m2), start_index + 1, index);
              assert false == mem(index, map(snd, m1));
            } else {
              insync_nonnone_index_in_ma_mb(t, m1, m2, vk1, vk2,
                                            index, start_index + 1);
            }
          case some(v):
            if (start_index == index) {
              map_has_the_value(m1, vk1(v));
              map_has_the_value(m2, vk2(v));
            } else {
              insync_no_dup_indexes_ma_mb(vals, m1, m2, vk1, vk2, start_index);
              insync_no_dup_indexes_ma_mb(t, map_erase_fp(m1, vk1(v)),
                                          map_erase_fp(m2, vk2(v)),
                                          vk1, vk2, start_index + 1);
              insync_nonnone_index_in_ma_mb(t, map_erase_fp(m1, vk1(v)),
                                            map_erase_fp(m2, vk2(v)), vk1, vk2,
                                            index, start_index + 1);

              less_than_boundary_nonmem(map(snd, map_erase_fp(m1, vk1(v))),
                                        start_index + 1, start_index);
              less_than_boundary_nonmem(map(snd, map_erase_fp(m2, vk2(v))),
                                        start_index + 1, start_index);
              map_erase_removes_index(m1, vk1(v));
              map_erase_removes_index(m2, vk2(v));
              neq_mem_remove(index, map_get_fp(m1, vk1(v)), map(snd, m1));
              neq_mem_remove(index, map_get_fp(m2, vk2(v)), map(snd, m2));
            }
        }
    }
  }

@*/

/*@
  lemma void dmap_nonnone_index_in_ma_mb<t1,t2,vt>(list<pair<t1, int> > ma,
                                                   list<pair<t2, int> > mb,
                                                   list<option<vt> > vals,
                                                   int index)
  requires dmappingp(dmap(ma, mb, vals), ?kp1, ?kp2, ?hsh1, ?hsh2,
                     ?fvp, ?bvp, ?rof, ?vsz,
                     ?vk1, ?vk2, ?recp1, ?recp2, ?mp) &*&
           0 <= index &*& index < length(vals);
  ensures dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz,
                    vk1, vk2, recp1, recp2, mp) &*&
          (mem(index, map(snd, ma)) ==
           (nth(index, vals) != none)) &*&
          (mem(index, map(snd, mb)) ==
           (nth(index, vals) != none));
  {
    open dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                   fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
    insync_nonnone_index_in_ma_mb(vals, ma, mb, vk1, vk2, index, 0);
    close dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void dmap_no_dup_keys<t1,t2,vt>(list<pair<t1,int> > ma,
                                        list<pair<t2, int> > mb,
                                        list<option<vt> > vals)
  requires dmappingp(dmap(ma, mb, vals), ?kp1, ?kp2, ?hsh1, ?hsh2,
                     ?fvp, ?bvp, ?rof, ?vsz,
                     ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
  ensures dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz,
                    vk1, vk2, recp1, recp2, mp) &*&
          true == no_dups(map(fst, ma)) &*&
          true == no_dups(map(fst, mb));
  {
    open dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                   fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
    map_no_dup_keys(ma);
    map_no_dup_keys(mb);
    close dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void mem_unerase<kt>(list<pair<kt, int> > m, kt k1, kt k2)
  requires true == mem(k1, map(fst, map_erase_fp(m, k2)));
  ensures true == mem(k1, map(fst, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key == k2) {
          } else {
            if (key != k1)
              mem_unerase(t, k1, k2);
          }
        }
    }
  }
  @*/


/*@
  lemma void no_no_dups_unerase<kt>(list<pair<kt, int> > m, kt k)
  requires false == no_dups(map(fst, map_erase_fp(m, k)));
  ensures false == no_dups(map(fst, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (mem(key, map(fst, map_erase_fp(t, k)))) {
            mem_unerase(t, key, k);
          } else {
            if (key != k)
              no_no_dups_unerase(t, k);
          }
        }
    }
  }
  @*/

/*@
  lemma void insync_has_val_has_key<t1,t2,vt>(list<option<vt> > vals,
                                              list<pair<t1, int> > m1,
                                              list<pair<t2, int> > m2,
                                              fixpoint (vt, t1) vk1,
                                              fixpoint (vt, t2) vk2,
                                              int start_index,
                                              vt v)
  requires true == mem(some(v), vals) &*&
           true == insync_fp(vals, m1, m2, vk1, vk2, start_index);
  ensures true == mem(vk1(v), map(fst, m1));
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            insync_has_val_has_key(t, m1, m2, vk1, vk2, start_index + 1, v);
          case some(x):
            if (x == v) {
              map_has_to_mem(m1, vk1(v));
            } else {
              insync_has_val_has_key(t, map_erase_fp(m1, vk1(x)),
                                     map_erase_fp(m2, vk2(x)),
                                     vk1, vk2, start_index + 1, v);
              mem_unerase(m1, vk1(v), vk1(x));
            }
        }
    }
  }
  @*/

/*@
  lemma void mem_erase_to_dup<kt>(list<pair<kt, int> > m, kt k)
  requires true == mem(k, map(fst, map_erase_fp(m, k)));
  ensures false == no_dups(map(fst, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, ind):
          if (key == k) {
          } else {
            mem_erase_to_dup(t, k);
          }
        }
    }
  }
  @*/

/*@
  lemma void insync_find_dup_key<t1,t2,vt>(list<option<vt> > vals,
                                           list<pair<t1, int> > m1,
                                           list<pair<t2, int> > m2,
                                           fixpoint (vt, t1) vk1,
                                           fixpoint (vt, t2) vk2,
                                           int start_index)
  requires true == insync_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           false == opt_no_dups(vals);
  ensures false == no_dups(map(fst, m1));
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            insync_find_dup_key(t, m1, m2, vk1, vk2, start_index + 1);
          case some(v):
            if (mem(some(v), t)) {
              insync_has_val_has_key(t, map_erase_fp(m1, vk1(v)),
                                     map_erase_fp(m2, vk2(v)),
                                     vk1, vk2, start_index + 1, v);
              assert true == mem(vk1(v), map(fst, map_erase_fp(m1, vk1(v))));
              mem_erase_to_dup(m1, vk1(v));
            } else {
              insync_find_dup_key(t, map_erase_fp(m1, vk1(v)),
                                  map_erase_fp(m2, vk2(v)),
                                  vk1, vk2, start_index + 1);
              no_no_dups_unerase(m1, vk1(v));
            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_no_dup_vals<t1,t2,vt>(list<pair<t1,int> > ma,
                                        list<pair<t2, int> > mb,
                                        list<option<vt> > vals)
  requires dmappingp(dmap(ma, mb, vals), ?kp1, ?kp2, ?hsh1, ?hsh2,
                     ?fvp, ?bvp, ?rof, ?vsz,
                     ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
  ensures dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz,
                    vk1, vk2, recp1, recp2, mp) &*&
          true == opt_no_dups(vals);
  {
    open dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                   fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
    if (!opt_no_dups(vals)) {
      insync_find_dup_key(vals, ma, mb, vk1, vk2, 0);
      map_no_dup_keys(ma);
    }
    close dmappingp(dmap(ma, mb, vals), kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void nonempty_indexes_bounds<vt>(list<option<vt> > lst, int start)
  requires true;
  ensures true == forall(nonempty_indexes_fp(lst, start), (ge)(start)) &*&
          true == forall(nonempty_indexes_fp(lst, start), (lt)(start + length(lst)));
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
          case some(x):
        }
        nonempty_indexes_bounds(t, start + 1);
        ge_le_ge(nonempty_indexes_fp(t, start+1), start + 1, start);
    }
  }
  @*/

/*@
  lemma void dmap_all_used_indexes_used<t1,t2,vt>(list<pair<t1,int> > ma,
                                                  list<pair<t2,int> > mb,
                                                  list<option<vt> > vals)
  requires true;
  ensures true == forall(dmap_indexes_used_fp(dmap(ma, mb, vals)),
                         (dmap_index_used_fp)(dmap(ma, mb, vals)));
  {
    list<int> used_indices = dmap_indexes_used_fp(dmap(ma, mb, vals));
    nonempty_indexes_bounds(vals, 0);
    for (int i = length(used_indices); 0 < i; --i)
      invariant true == forall(drop(i, used_indices),
                               (dmap_index_used_fp)(dmap(ma, mb, vals))) &*&
                0 <= i &*& i <= length(used_indices);
      decreases i;
    {
      forall_nth(used_indices, (ge)(0), i - 1);
      forall_nth(used_indices, (lt)(length(vals)), i - 1);
      dmap_indexes_contain_index_used(dmap(ma, mb, vals),
                                      nth(i-1, used_indices));
      drop_cons(used_indices, i - 1);
    }
  }
@*/

/*@
  lemma void non_mem_erase<kt>(list<pair<kt, int> > m, kt k1, kt k2)
  requires false == mem(k1, map(fst,m));
  ensures false == mem(k1, map(fst,map_erase_fp(m, k2)));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k2) non_mem_erase(t, k1, k2);
        }
    }
  }
  @*/


/*@
  lemma void map_erase_still_no_dup_keys<kt>(list<pair<kt, int> > m, kt k)
  requires true == no_dups(map(fst,m));
  ensures true == no_dups(map(fst,map_erase_fp(m, k)));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) {
            map_erase_still_no_dup_keys(t, k);
            non_mem_erase(t, key, k);
          }
        }
    }
  }
  @*/

/*@
  lemma void self_consistent_mem_keys<t1,t2,vt>(list<option<vt> > vals,
                                                list<pair<t1, int> > m1,
                                                list<pair<t2, int> > m2,
                                                fixpoint (vt,t1) vk1,
                                                fixpoint (vt,t2) vk2,
                                                int start_index,
                                                int index)
  requires true == dmap_self_consistent_fp(vals, m1, m2, vk1, vk2,
                                           start_index) &*&
           0 <= index - start_index &*&
           index - start_index < length(vals) &*&
           nth(index - start_index, vals) == some(?val);
  ensures true == mem(vk1(val), map(fst, m1)) &*&
          true == mem(vk2(val), map(fst, m2));
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            self_consistent_mem_keys(t, m1, m2, vk1, vk2,
                                     start_index + 1, index);
          case some(v):
            if (index == start_index) {
              map_has_to_mem(m1, vk1(val));
              map_has_to_mem(m2, vk2(val));
            } else {
              self_consistent_mem_keys(t, map_erase_fp(m1, vk1(v)),
                                       map_erase_fp(m2, vk2(v)),
                                       vk1, vk2,
                                       start_index + 1,
                                       index);
              mem_unerase(m1, vk1(val), vk1(v));
              mem_unerase(m2, vk2(val), vk2(v));
            }
        }
    }
  }
  @*/


/*@
  lemma void no_dups_consistent_these_keys_differ<t1,t2,vt>
               (list<option<vt> > vals,
                list<pair<t1, int> > m1,
                list<pair<t2, int> > m2,
                fixpoint (vt,t1) vk1,
                fixpoint (vt,t2) vk2,
                int start_index,
                int index)
  requires true == dmap_self_consistent_fp(vals, m1, m2,
                                           vk1, vk2, start_index) &*&
           true == no_dups(map(fst, m1)) &*&
           true == no_dups(map(fst, m2)) &*&
           0 < index - start_index &*&
           index - start_index < length(vals) &*&
           nth(index - start_index, vals) == some(?v) &*&
           nth(0, vals) == some(?value);
  ensures vk1(v) != vk1(value) &*&
          vk2(v) != vk2(value);
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
          case some(xxx):
            assert xxx == value;
            self_consistent_mem_keys(t, map_erase_fp(m1, vk1(value)),
                                     map_erase_fp(m2, vk2(value)),
                                     vk1, vk2, start_index + 1, index);
            if (vk1(v) == vk1(value)) {
              mem_erase_to_dup(m1, vk1(v));
              assert false;
            }
            if (vk2(v) == vk2(value)) {
              mem_erase_to_dup(m2, vk2(v));
              assert false;
            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_sconsist_indexes_right_hlp<t1,t2,vt>(list<option<vt> > vals,
                                                       list<pair<t1, int> > m1,
                                                       list<pair<t2, int> > m2,
                                                       fixpoint (vt,t1) vk1,
                                                       fixpoint (vt,t2) vk2,
                                                       int start_index,
                                                       int index)
  requires true == dmap_self_consistent_fp(vals, m1, m2,
                                           vk1, vk2, start_index) &*&
           0 <= index - start_index &*&
           index - start_index < length(vals) &*&
           nth(index - start_index, vals) == some(?v) &*&
           true == no_dups(map(fst, m1)) &*&
           true == no_dups(map(fst, m2));
  ensures map_get_fp(m1, vk1(v)) == index &*&
          map_get_fp(m2, vk2(v)) == index;
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            assert index != start_index;
            dmap_sconsist_indexes_right_hlp(t, m1, m2,
                                            vk1, vk2, start_index + 1,
                                            index);
          case some(value):
            if (index == start_index) {
            } else {
              map_erase_still_no_dup_keys(m1, vk1(value));
              map_erase_still_no_dup_keys(m2, vk2(value));
              dmap_sconsist_indexes_right_hlp(t, map_erase_fp(m1, vk1(value)),
                                              map_erase_fp(m2, vk2(value)),
                                              vk1, vk2, start_index + 1,
                                              index);
              no_dups_consistent_these_keys_differ
                (vals, m1, m2, vk1, vk2, start_index, index);
              map_erase_get_unrelevant(m1, vk1(value), vk1(v));
              map_erase_get_unrelevant(m2, vk2(value), vk2(v));
            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_consistent_right_indexes<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                     fixpoint (vt,t1) vk1,
                                                     fixpoint (vt,t2) vk2,
                                                     int index)
  requires true == dmap_self_consistent_integral_fp(m, vk1, vk2) &*&
           true == dmap_index_used_fp(m, index) &*&
           0 <= index &*& index < dmap_cap_fp(m);
  ensures dmap_get_k1_fp(m, vk1(dmap_get_val_fp(m, index))) == index &*&
          dmap_get_k2_fp(m, vk2(dmap_get_val_fp(m, index))) == index;
  {
    switch(m) { case dmap(m1, m2, vals):
      dmap_sconsist_indexes_right_hlp(vals, m1, m2, vk1, vk2, 0, index);
    }
  }
  @*/

/*@
  lemma void dmap_pred_self_consistent<t1,t2,vt>(dmap<t1,t2,vt> m)
  requires dmappingp<t1,t2,vt>(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                               ?fvp, ?bvp, ?rof, ?vsz,
                               ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
  ensures dmappingp<t1,t2,vt>(m, kp1, kp2, hsh1, hsh2, fvp,
                              bvp, rof, vsz, vk1, vk2, recp1, recp2, mp) &*&
          true == dmap_self_consistent_integral_fp(m, vk1, vk2);
  {
    open dmappingp(m, kp1, kp2, hsh1, hsh2,
                   fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
    switch(m) { case dmap(m1, m2, vals):
      map_no_dup_keys(m1);
      map_no_dup_keys(m2);
    }
    close dmappingp(m, kp1, kp2, hsh1, hsh2,
                    fvp, bvp, rof, vsz, vk1, vk2, recp1, recp2, mp);
  }
  @*/

/*@
  lemma void dmap_erase_self_consistent_hlp<t1,t2,vt>(list<option<vt> > vals,
                                                      list<pair<t1, int> > m1,
                                                      list<pair<t2, int> > m2,
                                                      fixpoint (vt,t1) vk1,
                                                      fixpoint (vt,t2) vk2,
                                                      int start_index,
                                                      int index)
  requires true == dmap_self_consistent_fp(vals, m1, m2, vk1, vk2, start_index) &*&
           0 <= index - start_index &*&
           index - start_index < length(vals) &*&
           nth(index - start_index, vals) == some(?value) &*&
           true == no_dups(map(fst, m1)) &*&
           true == no_dups(map(fst, m2));
  ensures true == dmap_self_consistent_fp(update(index - start_index,
                                                 none, vals),
                                          map_erase_fp(m1, vk1(value)),
                                          map_erase_fp(m2, vk2(value)),
                                          vk1, vk2, start_index);
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
            dmap_erase_self_consistent_hlp(t, m1, m2, vk1, vk2,
                                           start_index + 1,
                                           index);
          case some(v):
            if (index == start_index) {
            } else {
              map_erase_still_no_dup_keys(m1, vk1(v));
              map_erase_still_no_dup_keys(m2, vk2(v));
              dmap_erase_self_consistent_hlp(t,
                                             map_erase_fp(m1, vk1(v)),
                                             map_erase_fp(m2, vk2(v)),
                                             vk1, vk2,
                                             start_index + 1,
                                             index);
              no_dups_consistent_these_keys_differ
                (vals, m1, m2, vk1, vk2, start_index, index);
              map_erase_has_unrelevant(m1, vk1(value), vk1(v));
              map_erase_has_unrelevant(m2, vk2(value), vk2(v));
              map_erase_get_unrelevant(m1, vk1(value), vk1(v));
              map_erase_get_unrelevant(m2, vk2(value), vk2(v));
              map_erase_erase_swap(m1, vk1(value), vk1(v));
              map_erase_erase_swap(m2, vk2(value), vk2(v));

            }
        }
    }
  }
  @*/

/*@
  lemma void dmap_erase_self_consistent<t1,t2,vt>(dmap<t1,t2,vt> m,
                                                  int index,
                                                  fixpoint (vt,t1) vk1,
                                                  fixpoint (vt,t2) vk2)
  requires true == dmap_self_consistent_integral_fp(m, vk1, vk2) &*&
           true == dmap_index_used_fp(m, index);
  ensures true == dmap_self_consistent_integral_fp
                    (dmap_erase_fp(m, index, vk1, vk2), vk1, vk2);
  {
    switch(m) { case dmap(m1, m2, vals):
      dmap_erase_self_consistent_hlp(vals, m1, m2, vk1, vk2, 0, index);
      map_erase_still_no_dup_keys(m1, vk1(get_some(nth(index, vals))));
      map_erase_still_no_dup_keys(m2, vk2(get_some(nth(index, vals))));
    }
  }
  @*/
