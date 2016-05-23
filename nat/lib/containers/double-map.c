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
  int *inds_a;
  map_keys_equality *eq_a;
  map_key_hash *hsh_a;

  int *bbs_b;
  void **kps_b;
  int *khs_b;
  int *inds_b;
  map_keys_equality *eq_b;
  map_key_hash *hsh_b;

  dmap_extract_keys *exk;
  dmap_pack_keys *pk;

  int n_vals;
  int capacity;
};

/*@
  predicate valsp<vt>(void* values, int val_size,
                      predicate (void*,vt) fvp,
                      predicate (void*,vt) bvp,
                      int length, list<option<vt> > vals) =
     switch(vals) {
       case nil: return length == 0;
       case cons(h,t):
         return switch(h) {
           case none: return chars(values, val_size, _) &*&
                             valsp(values + val_size,
                                   val_size, fvp, bvp, length-1, t);
           case some(v): return [0.5]fvp(values, v) &*&
                                [0.5]bvp(values, v) &*&
                             valsp(values + val_size,
                                   val_size, fvp, bvp, length-1, t);
         };
     };

  fixpoint bool insync_fp<t1,t2,vt>(list<option<vt> > vals,
                                    list<pair<t1,int> > m1,
                                    list<pair<t2,int> > m2,
                                    fixpoint (vt,t1) vk1,
                                    fixpoint (vt,t2) vk2,
                                    int start_index) {
    switch(vals) {
      case nil: return m1 == empty_map_fp<t1,int>() &&
                       m2 == empty_map_fp<t2,int>();
      case cons(h,t):
        return switch(h) {
          case none: return insync_fp(t, m1, m2, vk1, vk2, start_index + 1);
          case some(v):
            return map_has_fp(m1, vk1(v)) &&
                   map_get_fp(m1, vk1(v)) == start_index &&
                   map_has_fp(m2, vk2(v)) &&
                   map_get_fp(m2, vk2(v)) == start_index &&
                   insync_fp(t, map_erase_fp(m1, vk1(v)),
                             map_erase_fp(m2, vk2(v)),
                             vk1, vk2, start_index+1);
        };
    }
  }

  predicate dmappingp<t1,t2,vt>(dmap<t1,t2,vt> m,
                                predicate (void*;t1) keyp1,
                                predicate (void*;t2) keyp2,
                                fixpoint (t1,int) hsh1,
                                fixpoint (t2,int) hsh2,
                                predicate (void*,vt) full_vp,
                                predicate (void*,vt) bare_vp,
                                fixpoint (void*,void*,void*,bool) right_offsets,
                                int val_size,
                                fixpoint (vt,t1) vk1,
                                fixpoint (vt,t2) vk2,
                                fixpoint (t1,int,bool) recp1,
                                fixpoint (t2,int,bool) recp2,
                                int capacity,
                                struct DoubleMap* mp) =
    malloc_block_DoubleMap(mp) &*&
    mp->value_size |-> val_size &*&
    0 < val_size &*& val_size < 4096 &*&
    mp->cpy |-> ?v_cpy &*&
    [_]is_uq_value_copy<vt>(v_cpy, full_vp, val_size) &*&
    mp->dstr |-> ?v_destr &*&
    [_]is_uq_value_destr<vt>(v_destr, full_vp, val_size) &*&
    mp->values |-> ?values &*&
    valsp(values, val_size, full_vp, bare_vp, capacity, ?val_arr) &*&
    malloc_block(values, val_size*capacity) &*&
    mp->bbs_a |-> ?bbs_a &*& malloc_block_ints(bbs_a, capacity) &*&
    mp->kps_a |-> ?kps_a &*& malloc_block_pointers(kps_a, capacity) &*&
    mp->khs_a |-> ?khs_a &*& malloc_block_ints(khs_a, capacity) &*&
    mp->inds_a |-> ?inds_a &*& malloc_block_ints(inds_a, capacity) &*&
    mapping(?ma, ?addrsa, keyp1, recp1, hsh1, capacity,
            bbs_a, kps_a, khs_a, inds_a) &*&
    mp->eq_a |-> ?eq_a &*&
    [_]is_map_keys_equality<t1>(eq_a, keyp1) &*&
    mp->hsh_a |-> ?hsh_a &*&
    [_]is_map_key_hash<t1>(hsh_a, keyp1, hsh1) &*&
    mp->bbs_b |-> ?bbs_b &*& malloc_block_ints(bbs_b, capacity) &*&
    mp->kps_b |-> ?kps_b &*& malloc_block_pointers(kps_b, capacity) &*&
    mp->khs_b |-> ?khs_b &*& malloc_block_ints(khs_b, capacity) &*&
    mp->inds_b |-> ?inds_b &*& malloc_block_ints(inds_b, capacity) &*&
    mapping(?mb, ?addrsb, keyp2, recp2, hsh2, capacity,
            bbs_b, kps_b, khs_b, inds_b) &*&
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
    mp->n_vals |-> dmap_size_fp(m) &*&
    0 <= capacity &*& capacity < 4096 &*&
    values + val_size*capacity <= (void*)UINTPTR_MAX &*&
    true == insync_fp(val_arr, ma, mb, vk1, vk2, 0) &*&
    m == dmap(ma, mb, val_arr);
  @*/

/*@
  lemma void empty_valsp<vt>(void* values, int val_size,
                             predicate (void*,vt) fvp,
                             predicate (void*,vt) bvp, nat len)
  requires chars(values, val_size*int_of_nat(len), _) &*&
           0 < val_size;
  ensures valsp(values, val_size, fvp, bvp, int_of_nat(len),
                empty_vals_fp(len));
  {
    switch(len) {
      case zero:
        close valsp(values, val_size, fvp, bvp, 0, nil);
        return;
      case succ(n):
        assume(val_size < val_size*int_of_nat(len)); //TODO
        assume(val_size*int_of_nat(len) - val_size == val_size*int_of_nat(n));
        chars_split(values, val_size);
        empty_valsp(values + val_size, val_size, fvp, bvp, n);
        close valsp(values, val_size, fvp, bvp, int_of_nat(len),
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

int dmap_allocate/*@ <K1,K2,V> @*/
                 (map_keys_equality* eq_a, map_key_hash* hsh_a,
                  map_keys_equality* eq_b, map_key_hash* hsh_b,
                  int value_size, uq_value_copy* v_cpy,
                  uq_value_destr* v_destr,
                  dmap_extract_keys* dexk,
                  dmap_pack_keys* dpk,
                  int capacity,
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
             0 < capacity &*& capacity < 4096; @*/
/*@ ensures result == 0 ?
            (*map_out |-> old_map_out) :
            (*map_out |-> ?mapp &*&
             result == 1 &*&
             dmappingp<K1,K2,V>(empty_dmap_fp(capacity), keyp1,
                                keyp2, hsh1, hsh2, fvp, bvp, rof, value_size,
                                vk1, vk2, recp1, recp2,
                                capacity, mapp)); @*/
{
  //@ open dmap_key_val_types(?def_k1, ?def_k2, ?def_val);
  //@ open dmap_record_property1(_);
  //@ open dmap_record_property2(_);
  struct DoubleMap* old_map_val = *map_out;
  struct DoubleMap* map_alloc = malloc(sizeof(struct DoubleMap));
  if (map_alloc == NULL) return 0;
  *map_out = (struct DoubleMap*) map_alloc;

  //@ mul_bounds(value_size, 4096, capacity, 4096);
  uint8_t* vals_alloc = malloc(value_size*capacity);
  if (vals_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->values = vals_alloc;
  int* bbs_a_alloc = malloc(sizeof(int)*capacity);
  if (bbs_a_alloc == NULL) {
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_a = bbs_a_alloc;
  void** kps_a_alloc = malloc(sizeof(void*)*capacity);
  if (kps_a_alloc == NULL) {
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_a = kps_a_alloc;
  int* khs_a_alloc = malloc(sizeof(int)*capacity);
  if (khs_a_alloc == NULL) {
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_a = khs_a_alloc;
  int* inds_a_alloc = malloc(sizeof(int)*capacity);
  if (inds_a_alloc == NULL) {
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->inds_a = inds_a_alloc;
  int* bbs_b_alloc = malloc(sizeof(int)*capacity);
  if (bbs_b_alloc == NULL) {
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->bbs_b = bbs_b_alloc;
  void** kps_b_alloc = malloc(sizeof(void*)*capacity);
  if (kps_b_alloc == NULL) {
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->kps_b = kps_b_alloc;
  int* khs_b_alloc = malloc(sizeof(int)*capacity);
  if (khs_b_alloc == NULL) {
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs_b = khs_b_alloc;
  int* inds_b_alloc = malloc(sizeof(int)*capacity);
  if (inds_b_alloc == NULL) {
    free(khs_b_alloc);
    free(kps_b_alloc);
    free(bbs_b_alloc);
    free(inds_a_alloc);
    free(khs_a_alloc);
    free(kps_a_alloc);
    free(bbs_a_alloc);
    free(vals_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->inds_b = inds_b_alloc;

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

  //@ close map_key_type(def_k1);
  //@ close map_key_hash(hsh1);
  //@ close map_record_property(recp1);
  map_initialize((*map_out)->bbs_a, (*map_out)->eq_a,
                 (*map_out)->kps_a, (*map_out)->khs_a, (*map_out)->inds_a,
                 (*map_out)->capacity);
  //@ close map_key_type(def_k2);
  //@ close map_key_hash(hsh2);
  //@ close map_record_property(recp2);
  map_initialize((*map_out)->bbs_b, (*map_out)->eq_b,
                 (*map_out)->kps_b, (*map_out)->khs_b, (*map_out)->inds_b,
                 (*map_out)->capacity);

  (*map_out)->n_vals = 0;
  //@ chars_limits((void*)vals_alloc);
  //@ empty_valsp(vals_alloc, value_size, fvp, bvp, nat_of_int(capacity));
  //@ empty_insync(nat_of_int(capacity), capacity, vk1, vk2);
  /*@ close dmappingp<K1,K2,V>(empty_dmap_fp<K1,K2,V>(capacity), keyp1, keyp2,
                               hsh1, hsh2,
                               fvp, bvp, rof, value_size,
                               vk1, vk2, recp1, recp2, capacity, *map_out);
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
                             int capacity,
                             int* busybits,
                             void** keyps,
                             int* k_hashes,
                             int* values) =
    mapping<kt>(m, addrs, keyp, recp, hash, capacity,
                busybits, keyps, k_hashes, values);
  @*/

int dmap_get_a/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             kp1(key, ?k1) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            kp1(key, k1) &*&
            (dmap_has_k1_fp(m, k1) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k1_fp(m, k1) &*&
              true == rp1(k1, ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  map_key_hash *hsh_a = map->hsh_a;
  //@ map_key_hash *hsh_b = map->hsh_b;
  //@ assert [?x]is_map_key_hash(hsh_b, kp2, hsh2);
  //@ close [x]hide_map_key_hash(map->hsh_b, kp2, hsh2);
  int hash = hsh_a(key);
  //@ open [x]hide_map_key_hash(map->hsh_b, kp2, hsh2);
  int rez = map_get(map->bbs_a, map->kps_a, map->khs_a, map->inds_a, key,
                    map->eq_a, hash, index,
                    map->capacity);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  return rez;
}

int dmap_get_b/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* key, int* index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             kp2(key, ?k2) &*&
             *index |-> ?i; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            kp2(key, k2) &*&
            (dmap_has_k2_fp(m, k2) ?
             (result == 1 &*&
              *index |-> ?ind &*&
              ind == dmap_get_k2_fp(m, k2) &*&
              true == rp2(k2, ind)) :
             (result == 0 &*& *index |-> i)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  map_key_hash *hsh_b = map->hsh_b;
  //@ map_key_hash *hsh_a = map->hsh_a;
  //@ assert [?x]is_map_key_hash(hsh_a, kp1, hsh1);
  //@ close [x]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  int hash = hsh_b(key);
  //@ open [x]hide_map_key_hash(map->hsh_a, kp1, hsh1);
  //@ int* bbs1 = map->bbs_a;
  //@ void** kps1 = map->kps_a;
  //@ int* khs1 = map->khs_a;
  //@ int* vals1 = map->inds_a;
  //@ assert mapping(?m1, ?addrs1, kp1, rp1, hsh1, cap, bbs1, kps1, khs1, vals1);
  //@ close hide_mapping(m1, addrs1, kp1, rp1, hsh1, cap, bbs1, kps1, khs1, vals1);
  return map_get(map->bbs_b, map->kps_b, map->khs_b, map->inds_b, key,
                 map->eq_b, hash, index,
                 map->capacity);
  //@ open hide_mapping(_, _, _, _, _, _, _, _, _, _);
  /*@ close dmappingp(m, kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
}

/*@
  lemma void extract_value<vt>(void* values, list<option<vt> > vals, int i)
  requires valsp(values, ?vsz, ?fvp, ?bvp, ?len, vals) &*&
           0 <= i &*& i < len;
  ensures valsp(values, vsz, fvp, bvp, i, take(i, vals)) &*&
          switch(nth(i, vals)) { case none : return chars(values+i*vsz, vsz, _);
                                 case some(x): return [0.5]fvp(values+i*vsz, x) &*&
                                                      [0.5]bvp(values+i*vsz, x); } &*&
          valsp(values+(i+1)*vsz, vsz, fvp, bvp, len-i-1, drop(i+1, vals));
  {
    open valsp(values, vsz, fvp, bvp, len, vals);
    switch(vals) {
      case nil: return;
      case cons(h,t):
        if (i == 0) {
        } else {
          extract_value(values + vsz, t, i-1);
        }
    }
    close valsp(values, vsz, fvp, bvp, i, take(i, vals));
  }
  @*/

/*@
  lemma void glue_values<vt>(void* values, list<option<vt> > vals, int i)
  requires valsp(values, ?vsz, ?fvp, ?bvp, i, take(i, vals)) &*&
           nth(i, vals) != none &*&
           [0.5]fvp(values+i*vsz, get_some(nth(i, vals))) &*&
           [0.5]bvp(values+i*vsz, get_some(nth(i, vals))) &*&
           valsp(values+(i+1)*vsz, vsz, fvp, bvp,
                 length(vals)-i-1, drop(i+1, vals)) &*&
           0 <= i &*& i < length(vals);
  ensures valsp(values, vsz, fvp, bvp, length(vals), vals);
  {
    switch(vals) {
      case nil:
        return;
      case cons(h,t):
        open valsp(values, vsz, fvp, bvp, i, take(i, vals));
        if (i == 0) {
        } else {
          glue_values(values + vsz, t, i-1);
        }
        close valsp(values, vsz, fvp, bvp, length(vals), vals);
    }
  }
  @*/

/*@
  lemma void vals_len_is_cap<vt>(list<option<vt> > vals, int capacity)
  requires valsp(?values, ?vsz, ?fvp, ?bvp, capacity, vals);
  ensures valsp(values, vsz, fvp, bvp, capacity, vals) &*&
          length(vals) == capacity;
  {
    open valsp(values, vsz, fvp, bvp, capacity, vals);
    switch(vals) {
      case nil:
        break;
      case cons(h,t):
        vals_len_is_cap(t, capacity-1);
    }
    close valsp(values, vsz, fvp, bvp, capacity, vals);
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
  predicate hide_half_bvp<vt>(predicate (void*,vt) bvp, void* addr, vt v) =
    [0.5]bvp(addr,v);
  @*/

int dmap_put/*@ <K1,K2,V> @*/(struct DoubleMap* map, void* value, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             fvp(value, ?v) &*&
             true == rp1(vk1(v), index) &*&
             true == rp2(vk2(v), index) &*&
             false == dmap_index_used_fp(m, index) &*&
             false == dmap_has_k1_fp(m, vk1(v)) &*&
             false == dmap_has_k2_fp(m, vk2(v)) &*&
             0 <= index &*& index < cap; @*/
/*@ ensures result == 1 &*&
            dmappingp<K1,K2,V>(dmap_put_fp(m, index, v, vk1, vk2),
                               kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            fvp(value, v);@*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  //@ void* values = map->values;
  //@ assert valsp(values, vsz, fvp, bvp, cap, ?vals);
  //@ vals_len_is_cap(vals, cap);
  void* key_a = 0;
  void* key_b = 0;
  //@ mul_bounds(index, cap, vsz, 4096);
  //@ mul_mono_strict(index, cap, vsz);
  //@ extract_value(map->values, vals, index);
  void* my_value = map->values + index*map->value_size;
  uq_value_copy* cpy = map->cpy;
  cpy(my_value, value);

  dmap_extract_keys *exk = map->exk;
  exk(my_value, &key_a, &key_b);

  map_key_hash *hsh_a = map->hsh_a;
  int hash1 = hsh_a(key_a);

  //@ assert mapping(?m1, ?addrs1, kp1, rp1, hsh1, cap, ?bbs1, ?kps1, ?khs1, ?vals1);
  //@ assert mapping(?m2, ?addrs2, kp2, rp2, hsh2, cap, ?bbs2, ?kps2, ?khs2, ?vals2);
  //@ insync_has_not_nonfull(vals, m1, m2, vk1, vk2, cap, index);
  //@ assert map_size_fp(m1) < cap;

  int ret1 = map_put(map->bbs_a, map->kps_a, map->khs_a,
                     map->inds_a, key_a,
                     hash1,
                     index, map->capacity);

  //@ assert ret1 == 1;
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
                         kp1, rp1, hsh1, cap, bbs1, kps1, khs1, vals1);
    @*/
  int ret2 = map_put(map->bbs_b, map->kps_b, map->khs_b,
                      map->inds_b, key_b,
                      hash2,
                      index, map->capacity);
  //@ open hide_mapping(_, _, kp1, rp1, hsh1, cap, bbs1, kps1, khs1, vals1);
  //@ assert ret2 == 1;
  ++map->n_vals;
  dmap_pack_keys *pk = map->pk;
  //@ close hide_half_bvp(bvp, my_value, v);
  pk(my_value, key_a, key_b);
  //@ open hide_half_bvp(bvp, my_value, v);
  //@ take_update_unrelevant(index, index, some(v), vals);
  //@ drop_update_unrelevant(index+1, index, some(v), vals);
  //@ nth_update(index, index, some(v), vals);
  //@ glue_values(map->values, update(index, some(v), vals), index);

  //@ update_insync(vals, m1, m2, index, v, vk1, vk2, cap);

  /*@ close dmappingp(dmap_put_fp(m, index, v, vk1, vk2),
                      kp1, kp2, hsh1, hsh2,
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  return 1;
}

void dmap_get_value/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index,
                                     void* value_out)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             chars(value_out, vsz, _) &*&
             0 <= index &*& index < cap; @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            fvp(value_out, dmap_get_val_fp(m, index)); @*/
{
  /*@ open dmappingp(m, kp1, kp2, hsh1, hsh2,
                     fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
  //@ void* values = map->values;
  //@ assert valsp(values, vsz, fvp, bvp, cap, ?vals);
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
                      fvp, bvp, rof, vsz, vk1, vk2, rp1, rp2, cap, map); @*/
}

int dmap_erase/*@ <K1,K2,V> @*/(struct DoubleMap* map, int index)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map) &*&
             dmap_index_used_fp(m, index) == true &*&
             0 <= index &*& index < cap; @*/
/*@ ensures result == 1 &*&
            dmappingp<K1,K2,V>(dmap_erase_fp(m, index, vk1, vk2),
                               kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map); @*/
{
  void* key_a = 0;
  void* key_b = 0;
  map->exk(map->values + index*map->value_size, &key_a, &key_b);
  int ret = map_erase(map->bbs_a, map->kps_a, map->khs_a, key_a,
                      map->eq_a, map->hsh_a(key_a),
                      map->capacity, 0) &&
    map_erase(map->bbs_b, map->kps_b, map->khs_b, key_b,
              map->eq_b, map->hsh_b(key_b),
              map->capacity, 0);
  if (ret) --map->n_vals;
  return ret;
}

int dmap_size/*@ <K1,K2,V> @*/(struct DoubleMap* map)
/*@ requires dmappingp<K1,K2,V>(?m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                                ?fvp, ?bvp, ?rof, ?vsz,
                                ?vk1, ?vk2, ?rp1, ?rp2, ?cap, map); @*/
/*@ ensures dmappingp<K1,K2,V>(m, kp1, kp2, hsh1, hsh2,
                               fvp, bvp, rof, vsz,
                               vk1, vk2, rp1, rp2, cap, map) &*&
            result == dmap_size_fp(m); @*/
{
  return map->n_vals;
}

