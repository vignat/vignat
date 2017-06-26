#include <stdint.h>
#include <string.h>

#include "map-impl.h"
#include "lib/ignore.h"

//@ #include <list.gh>
//@ #include <listex.gh>
//@ #include <nat.gh>
//@ #include "stdex.gh"
//@ #include "nth_prop.gh"
//@ #include "modulo.gh"
//@ #include "map.gh"
//@ #include "natlist.gh"
//@ #include "chain-buckets.gh"


/*@
  fixpoint bool has_given_hash_fp<kt>(fixpoint (kt, int) hash,
                                      int pos, int capacity,
                                      pair<kt, nat> chain) {
    return pos == loop_fp(hash(fst(chain)), capacity);
  }

  fixpoint bool key_chains_start_on_hash_fp<kt>(list<bucket<kt> > buckets,
                                                int pos, int capacity,
                                                fixpoint (kt, int) hash) {
    switch(buckets) {
      case nil: return true;
      case cons(h,t):
        return switch(h) { case bucket(chains):
            return forall(chains, (has_given_hash_fp)(hash, pos, capacity)) &&
                   key_chains_start_on_hash_fp(t, pos + 1, capacity, hash);
          };
    }
  }
  @*/

static
int loop(int k, int capacity)
//@ requires 0 < capacity &*& 2*capacity < INT_MAX;
/*@ ensures 0 <= result &*& result < capacity &*&
            result == loop_fp(k, capacity); @*/
{
  int g = k%capacity;
  //@ div_mod(g, k, capacity);
  //@ assert(2*capacity< INT_MAX);
  int res = (g + capacity)%capacity;
  //@ div_mod_gt_0(res, g + capacity, capacity);
  return res;
}

/*@
  inductive hmap<kt> = hmap(list<option<kt> >, list<int>);

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash,
                         int capacity,
                         int* busybits,
                         list<void*> kps,
                         int* k_hashes;
                         hmap<kt> m);

  fixpoint list<option<kt> > hmap_ks_fp<kt>(hmap<kt> m) {
    switch(m) { case hmap(ks, khs): return ks; }
  }

  fixpoint int ks_size_fp<kt>(list<option<kt> > ks) {
    switch(ks) {
      case nil: return 0;
      case cons(h,t): return (h == none ? 0 : 1) + ks_size_fp(t);
    }
  }

  fixpoint int hmap_size_fp<kt>(hmap<kt> m) {
    return ks_size_fp(hmap_ks_fp(m));
  }

  fixpoint bool hmap_empty_cell_fp<kt>(hmap<kt> m, int index) {
    return (nth(index, hmap_ks_fp(m)) == none);
  }

  fixpoint bool hmap_exists_key_fp<kt>(hmap<kt> m, kt k) {
    return mem(some(k), hmap_ks_fp(m));
  }

  fixpoint int hmap_find_key_fp<kt>(hmap<kt> m, kt k) {
    return index_of(some(k), hmap_ks_fp(m));
  }

  fixpoint hmap<kt> hmap_put_key_fp<kt>(hmap<kt> m, int i, kt k, int hash) {
    switch(m) { case hmap(ks, khs):
      return hmap(update(i, some(k), ks), update(i, hash, khs));
    }
  }

  fixpoint hmap<kt> hmap_rem_key_fp<kt>(hmap<kt> m, int i) {
    switch(m) { case hmap(ks, khs):
      return hmap(update(i, none, ks), khs);
    }
  }

  @*/

/*@

  predicate pred_mapping<t>(list<void*> pts, list<int> bbs,
                            predicate (void*; t) pred;
                            list<option<t> > ks) =
    switch(bbs) {
      case nil:
        return ks == nil &*& pts == nil;
      case cons(h,t):
        return pts == cons(?pth,?ptt) &*&
          pred_mapping(ptt, t, pred, ?kt) &*&
          (h == 0 ? ks == cons(none, kt) :
             ([0.5]pred(pth, ?kh) &*& ks == cons(some(kh), kt)));
    };

  fixpoint bool hash_list<kt>(list<option<kt> > vals,
                             list<int> hashes,
                             fixpoint (kt, int) hash) {
    switch(vals) {
      case nil: return hashes == nil;
      case cons(h,t):
        return hash_list(t, tail(hashes), hash) &&
               hashes != nil &&
               (h == none || head(hashes) == hash(get_some(h)));
    }
  }

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash,
                         int capacity,
                         int* busybits,
                         list<void*> kps,
                         int* k_hashes;
                         hmap<kt> m) =
            0 < capacity &*& 2*capacity < INT_MAX &*&
            ints(busybits, capacity, ?bbs) &*&
            ints(k_hashes, capacity, ?khs) &*&
            pred_mapping(kps, bbs, keyp, ?ks) &*&
            true == opt_no_dups(ks) &*&
            true == hash_list(ks, khs, hash) &*&
            m == hmap(ks, khs);
@*/

/*@
  predicate buckets_ks_insync<kt>(int* chns, int capacity,
                                  list<bucket<kt> > buckets,
                                  fixpoint (kt,int) hash;
                                  list<option<kt> > ks) =
    ints(chns, capacity, buckets_get_chns_fp(buckets)) &*&
    true == buckets_ok(buckets) &*&
    true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash) &*&
    ks == buckets_get_keys_fp(buckets);
  @*/

/*@
  lemma void hmap_rem_preserves_no_dups<kt>(list<option<kt> > ks, int i)
  requires true == opt_no_dups(ks) &*& 0 <= i;
  ensures true == opt_no_dups(update(i, none, ks));
  {
    rem_preserves_opt_no_dups(ks, i);
  }

  lemma void hmap_rem_preserves_hash_list<kt>(list<option<kt> > vals,
                                              list<int> hashes,
                                              fixpoint (kt, int) hash,
                                              int i)
  requires true == hash_list(vals, hashes, hash) &*& 0 <= i;
  ensures true == hash_list(update(i, none, vals), hashes, hash);
  {
    switch(vals){
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          hmap_rem_preserves_hash_list(t, tail(hashes), hash, i-1);
        }
    }
  }
@*/


/*@
  lemma void hash_for_given_key<kt>(list<pair<kt, nat> > chains,
                                    fixpoint (kt,int) hash,
                                    int shift, int capacity,
                                    kt k)
  requires true == mem(k, map(fst, chains)) &*&
           true == forall(chains, (has_given_hash_fp)(hash, shift, capacity));
  ensures true == (loop_fp(hash(k), capacity) == shift);
  {
    switch(chains) {
      case nil:
      case cons(h,t):
        if (fst(h) == k) {
        } else {
          hash_for_given_key(t, hash, shift, capacity, k);
        }
    }
  }
  @*/

/*@
  lemma void overshoot_bucket<kt>(list<bucket<kt> > buckets, int shift,
                                  int capacity,
                                  fixpoint (kt,int) hash,
                                  kt k)
  requires true == key_chains_start_on_hash_fp(buckets, shift, capacity, hash) &*&
           loop_fp(hash(k), capacity) < shift &*& shift <= capacity &*&
           capacity - shift == length(buckets);
  ensures false == exists(buckets, (bucket_has_key_fp)(k));
  {
    switch(buckets) {
      case nil: return;
      case cons(bh,bt):
        switch(bh) { case bucket(chains):
          if (bucket_has_key_fp(k, bh)) {
              assert true == mem(k, map(fst, chains));
              assert true == forall(chains, (has_given_hash_fp)(hash, shift, capacity));
              hash_for_given_key(chains, hash, shift, capacity, k);
              assert true == (loop_fp(hash(k), capacity) == shift);
          }
          overshoot_bucket(bt, shift + 1, capacity, hash, k);
        }
    }
  }
  @*/

/*@
  lemma void no_hash_not_in_this_bucket<kt>(list<pair<kt, nat> > chains, kt k,
                                            int shift, int capacity,
                                            fixpoint (kt,int) hash)
  requires true == forall(chains, (has_given_hash_fp)(hash, shift, capacity)) &&
           shift != loop_fp(hash(k), capacity);
  ensures false == mem(k, map(fst, chains));
  {
    switch(chains) {
      case nil:
      case cons(h,t):
        if (fst(h) == k) {
          assert false;
        }
        no_hash_not_in_this_bucket(t, k, shift, capacity, hash);
    }
  }
  @*/

/*@
  lemma void wrong_hash_no_key<kt>(kt k, bucket<kt> bh, list<bucket<kt> > bt,
                                   int shift, int capacity,
                                   fixpoint (kt,int) hash)
  requires true == key_chains_start_on_hash_fp(cons(bh,bt), shift, capacity, hash) &*&
           shift != loop_fp(hash(k), capacity);
  ensures false == bucket_has_key_fp(k, bh);
  {
    switch(bh) { case bucket(chains):
      no_hash_not_in_this_bucket(chains, k, shift, capacity, hash);
    }
  }//took 10m
  @*/

/*@
  lemma void key_is_contained_in_the_bucket_rec<kt>(list<bucket<kt> > buckets,
                                                    list<pair<kt, nat> > acc,
                                                    int shift, int capacity,
                                                    fixpoint (kt,int) hash,
                                                    kt k)
  requires true == key_chains_start_on_hash_fp(buckets, shift, capacity, hash) &*&
           true == buckets_ok_rec(acc, buckets, capacity) &*&
           false == mem(k, map(fst, acc)) &*&
           0 <= shift &*& shift <= loop_fp(hash(k), capacity) &*&
           0 < capacity &*&
           capacity - shift == length(buckets) &*&
           false == mem(k, map(fst, get_wraparound(acc, buckets))) &*&
           buckets != nil;
  ensures loop_fp(hash(k), capacity) - shift < length(buckets) &*&
          mem(some(k), buckets_get_keys_rec_fp(acc, buckets)) ==
          bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity) - shift, buckets));
  {
    switch(buckets) {
      case nil: return;
      case cons(bh,bt):
        loop_lims(hash(k), capacity);
        assert true == ((loop_fp(hash(k), capacity) - shift) <= length(buckets));
        if (loop_fp(hash(k), capacity) == shift) {
          if (mem(some(k), buckets_get_keys_rec_fp(acc, buckets))) {
            some_bucket_contains_key_rec(acc, buckets, k);
            switch(bh) { case bucket(chains): }
            overshoot_bucket(bt, shift+1, capacity, hash, k);
            if (bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity) - shift, buckets))) {
            } else {
              assert false;
            }
          } else {
            if (bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity) - shift, buckets))) {
              in_this_bucket_then_in_the_map(buckets,
                                             loop_fp(hash(k), capacity) - shift,
                                             k, capacity, acc);
              assert false;
            } else {

            }
          }
        } else {
          assert true == (shift < loop_fp(hash(k), capacity));
          assert true == (shift + 1 < capacity);
          assert true == (1 < length(buckets));
          assert true == (0 < length(bt));
          switch(bt) {
            case nil:
            case cons(h,t):
          }
          switch(bh) { case bucket(chains): };
          wrong_hash_no_key(k, bh, bt, shift, capacity, hash);
          this_bucket_still_no_key(acc, bh, k);
          advance_acc_still_no_key(acc_at_this_bucket(acc, bh), k);
          key_is_contained_in_the_bucket_rec(bt, advance_acc
                                                   (acc_at_this_bucket(acc,
                                                                       bh)),
                                             shift + 1, capacity,
                                             hash, k);
          no_key_certainly_not_here(acc_at_this_bucket(acc, bh), k);
          assert some(k) != get_current_key_fp(acc_at_this_bucket(acc, bh));
          assert true == (bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity) - shift, buckets)) ==
                          bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity) - shift - 1, bt)));
        }
    }
  }

  @*/

/*@
  lemma void
  bucket_has_key_correct_hash<kt>(list<bucket<kt> > buckets, kt k,
                                  int start, int capacity,
                                  fixpoint (kt,int) hash)
  requires true == exists(buckets, (bucket_has_key_fp)(k)) &*&
           true == key_chains_start_on_hash_fp(buckets, start,
                                               capacity, hash) &*&
           start + length(buckets) == capacity;
  ensures true == bucket_has_key_fp(k, nth(loop_fp(hash(k),
                                                   capacity) - start,
                                           buckets));
  {
    switch(buckets) {
      case nil:
      case cons(bh,bt):
        switch(bh) { case bucket(chains):
          if (bucket_has_key_fp(k, bh)) {
            if (start != loop_fp(hash(k), capacity)) {
              no_hash_not_in_this_bucket(chains, k, start, capacity, hash);
            }
          } else {
            bucket_has_key_correct_hash(bt, k, start + 1, capacity, hash);
            if (loop_fp(hash(k), capacity) < start + 1) {
              overshoot_bucket(bt, start + 1, capacity, hash, k);
            }
          }
        }
    }
  }
  @*/


/*@
  @*/

/*@
  @*/

/*@
  lemma void key_is_contained_in_the_bucket<kt>(list<bucket<kt> > buckets,
                                                int capacity,
                                                fixpoint (kt,int) hash,
                                                kt k)
  requires true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash) &*&
           0 < capacity &*&
           true == buckets_ok(buckets) &*&
           length(buckets) == capacity;
  ensures mem(some(k), buckets_get_keys_fp(buckets)) ==
          bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity), buckets));
  {
    loop_lims(hash(k), capacity);
    if (mem(k, map(fst, get_wraparound(nil, buckets)))) {
      key_in_wraparound_then_key_in_a_bucket(buckets, k, nil);
      bucket_has_key_correct_hash(buckets, k, 0, capacity, hash);
      buckets_ok_wraparound_bounded_rec(get_wraparound(nil, buckets),
                                        buckets, capacity);
      buckets_ok_get_wraparound_idemp(buckets);
      key_in_wraparound_then_in_bucket(buckets, k);
    } else {
      buckets_ok_get_wraparound_idemp(buckets);
      key_is_contained_in_the_bucket_rec(buckets, get_wraparound(nil, buckets),
                                         0, capacity, hash, k);
    }
  }//110 mins
  @*/

/*@
  lemma void pred_mapping_same_len<t>(list<int> bbs, list<option<t> > ks)
  requires pred_mapping(?pts, bbs, ?pred, ks);
  ensures pred_mapping(pts, bbs, pred, ks) &*&
          length(bbs) == length(ks);
  {
    open pred_mapping(_, _, _, _);
    switch(bbs) {
      case nil:
        assert(ks == nil);
        break;
      case cons(h, t):
        pred_mapping_same_len(t, tail(ks));
    }
    close pred_mapping(pts, bbs, pred, ks);
  }

  lemma kt extract_pred_for_key<kt>(list<void*> kps_b,
                                    list<int> bbs_b,
                                    list<option<kt> > ks_b,
                                    int n, list<int> bbs,
                                    list<option<kt> > ks)
  requires pred_mapping(?kps, bbs, ?pred, ks) &*&
           pred_mapping(kps_b, bbs_b, pred, ks_b) &*&
           0 <= n &*& n < length(bbs) &*& nth(n, bbs) != 0;
  ensures nth(n, ks) == some(result) &*& [0.5]pred(nth(n, kps), result) &*&
          pred_mapping(drop(n+1, kps), drop(n+1, bbs), pred, drop(n+1, ks)) &*&
          pred_mapping(append(reverse(take(n, kps)), kps_b),
                       append(reverse(take(n, bbs)), bbs_b),
                       pred,
                       append(reverse(take(n, ks)), ks_b));
  {
    open pred_mapping(kps, _, _, _);
    switch(bbs) {
      case nil:
        assert(length(bbs) == 0);
        return default_value<kt>();
      case cons(bbh, bbt):
        switch(kps) {
          case nil: return default_value<kt>();
          case cons(kph, kpt):
            switch(ks) {
              case nil: return default_value<kt>();
              case cons(kh, kt) :
              if (n == 0) {
                switch(kh) {
                  case some(k):
                    return k;
                  case none: return default_value<kt>();
                }
              } else {
                close pred_mapping(cons(kph, kps_b), cons(bbh,bbs_b),
                                   pred, cons(kh, ks_b));
                append_reverse_take_cons(n,kph,kpt,kps_b);
                append_reverse_take_cons(n,bbh,bbt,bbs_b);
                append_reverse_take_cons(n,kh,kt,ks_b);
                return extract_pred_for_key(cons(kph,kps_b),
                                            cons(bbh,bbs_b),
                                            cons(kh, ks_b),
                                            n-1, bbt, kt);
              }
            }
        }
    }
  }

  lemma void reconstruct_pred_mapping<kt>(list<void*> kps1,
                                          list<int> bbs1,
                                          list<option<kt> > ks1,
                                          list<void*> kps2,
                                          list<int> bbs2,
                                          list<option<kt> > ks2)
  requires pred_mapping(kps1, bbs1, ?pred, ks1) &*&
           pred_mapping(kps2, bbs2, pred, ks2);
  ensures pred_mapping(append(reverse(kps1), kps2),
                       append(reverse(bbs1), bbs2),
                       pred,
                       append(reverse(ks1), ks2));
  {
    open pred_mapping(kps1, bbs1, pred, ks1);
    switch(bbs1) {
      case nil:
        assert(kps1 == nil);
        assert(ks1 == nil);
        return;
      case cons(bbh, bbt):
        append_reverse_tail_cons_head(kps1, kps2);
        append_reverse_tail_cons_head(bbs1, bbs2);
        append_reverse_tail_cons_head(ks1, ks2);
        close pred_mapping(cons(head(kps1), kps2), cons(bbh, bbs2),
                           pred, cons(head(ks1), ks2));
        reconstruct_pred_mapping(tail(kps1), bbt, tail(ks1),
                                 cons(head(kps1), kps2),
                                 cons(bbh, bbs2),
                                 cons(head(ks1), ks2));
    }
  }

  lemma void recover_pred_mapping<kt>(list<void*> kps, list<int> bbs,
                                      list<option<kt> > ks,
                                      int n)
  requires pred_mapping(reverse(take(n, kps)), reverse(take(n, bbs)),
                        ?pred, reverse(take(n, ks))) &*&
           nth(n, bbs) != 0 &*&
           [0.5]pred(nth(n, kps), ?k) &*&
           nth(n, ks) == some(k) &*&
           pred_mapping(drop(n+1, kps), drop(n+1, bbs),
                        pred, drop(n+1, ks)) &*&
           0 <= n &*& n < length(kps) &*&
           n < length(bbs) &*&
           n < length(ks);
  ensures pred_mapping(kps, bbs, pred, ks);
  {
    close pred_mapping(cons(nth(n, kps), drop(n+1,kps)),
                       cons(nth(n, bbs), drop(n+1,bbs)),
                       pred,
                       cons(nth(n, ks), drop(n+1, ks)));
    drop_n_plus_one(n, kps);
    drop_n_plus_one(n, bbs);
    drop_n_plus_one(n, ks);
    reconstruct_pred_mapping(reverse(take(n, kps)),
                             reverse(take(n, bbs)),
                             reverse(take(n, ks)),
                             drop(n, kps),
                             drop(n, bbs),
                             drop(n, ks));
  }

  lemma void ks_find_this_key<kt>(list<option<kt> > ks, int i, kt k)
  requires nth(i, ks) == some(k) &*& true == opt_no_dups(ks) &*&
           0 <= i &*& i < length(ks);
  ensures index_of(some(k), ks) == i;
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        if (h == some(k)) {
          no_dups_same(ks, k, i, 0);
          assert(i == 0);
          return;
        } else {
          ks_find_this_key(t, i-1, k);
        }
    }
  }

  lemma void hmap_find_this_key<kt>(hmap<kt> m, int i, kt k)
  requires nth(i, hmap_ks_fp(m)) == some(k) &*& true == opt_no_dups(hmap_ks_fp(m)) &*&
           0 <= i &*& i < length(hmap_ks_fp(m));
  ensures hmap_find_key_fp(m, k) == i;
  {
    ks_find_this_key(hmap_ks_fp(m), i, k);
  }

  lemma void no_hash_no_key<kt>(list<option<kt> > ks, list<int> hashes,
                                kt k, int i, fixpoint (kt,int) hash)
  requires true == hash_list(ks, hashes, hash) &*&
           nth(i, hashes) != hash(k) &*&
           0 <= i &*& i < length(ks);
  ensures nth(i, ks) != some(k);
  {
    switch(ks) {
      case nil:
        assert(hashes == nil);
        return;
      case cons(kh,kt):
        assert(hashes != nil);
        if (i == 0) {
          assert(nth(i, ks) == kh);
          if (kh == some(k)) {
            assert(head(hashes) == hash(k));
            nth_0_head(hashes);
            assert(nth(i, hashes) == head(hashes));
            assert(nth(i, hashes) == hash(k));
          }
          return;
        } else {
          nth_cons(i, tail(hashes), head(hashes));
          cons_head_tail(hashes);
          assert(nth(i, hashes) == nth(i-1,tail(hashes)));
          no_hash_no_key(kt, tail(hashes), k, i-1, hash);
        }
    }
  }
@*/

/*@
  lemma void no_bb_no_key<kt>(list<option<kt> > ks, list<int> bbs, int i)
  requires pred_mapping(?kps, bbs, ?pred, ks) &*& 0 <= i &*& i < length(ks) &*&
           nth(i, bbs) == 0;
  ensures pred_mapping(kps, bbs, pred, ks) &*& nth(i, ks) == none;
  {
    open pred_mapping(kps, bbs, pred, ks);
    switch(bbs) {
      case nil: ;
      case cons(bbh,bbt):
        if (i == 0) {
          nth_0_head(bbs);
          nth_0_head(ks);
        } else {
          no_bb_no_key(tail(ks), tail(bbs), i-1);
        }
    }
    close pred_mapping(kps, bbs, pred, ks);
  }
@*/


/*@
  lemma void up_to_neq_non_mem<t>(list<t> l, t x)
  requires true == up_to(nat_of_int(length(l)), (nthProp)(l, (neq)(x)));
  ensures false == mem(x, l);
  {
    switch(l) {
      case nil:
      case cons(h,t):
        up_to_nth_uncons(h, t, nat_of_int(length(t)), (neq)(x));
        up_to_neq_non_mem(t, x);
    }
  }
  @*/


/*@
  lemma void no_key_found<kt>(list<option<kt> > ks, kt k)
  requires true == up_to(nat_of_int(length(ks)), (nthProp)(ks, (neq)(some(k))));
  ensures false == mem(some(k), ks);
  {
    up_to_neq_non_mem(ks, some(k));
  }
@*/

static
int find_key/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* chns,
                         void* keyp, map_keys_equality* eq, int key_hash,
                         int capacity)
/*@ requires hmapping<kt>(?kpr, ?hsh, capacity, busybits, ?kps, k_hashes, ?hm) &*&
             buckets_ks_insync(chns, capacity, ?buckets, hsh,
                                 hmap_ks_fp(hm)) &*&
             pointers(keyps, capacity, kps) &*&
             [?kfr]kpr(keyp, ?k) &*&
             hsh(k) == key_hash &*&
             [?f]is_map_keys_equality<kt>(eq, kpr); @*/
/*@ ensures hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm) &*&
            buckets_ks_insync(chns, capacity, buckets, hsh,
                                hmap_ks_fp(hm)) &*&
            pointers(keyps, capacity, kps) &*&
            [kfr]kpr(keyp, k) &*&
            [f]is_map_keys_equality<kt>(eq, kpr) &*&
            (hmap_exists_key_fp(hm, k) ?
             (result == hmap_find_key_fp(hm, k)) :
             (result == -1)); @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ open buckets_ks_insync(chns, capacity, buckets, hsh, hmap_ks_fp(hm));
  //@ assert ints(chns, capacity, ?chnlist);
  //@ assert pred_mapping(kps, ?bbs, kpr, ?ks);
  //@ assert hm == hmap(ks, ?khs);
  int start = loop(key_hash, capacity);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant pred_mapping(kps, bbs, kpr, ks) &*&
                  ints(busybits, capacity, bbs) &*&
                  ints(k_hashes, capacity, khs) &*&
                  ints(chns, capacity, chnlist) &*&
                  pointers(keyps, capacity, kps) &*&
                  0 <= i &*& i <= capacity &*&
                  [f]is_map_keys_equality<kt>(eq, kpr) &*&
                  [kfr]kpr(keyp, k) &*&
                  hsh(k) == key_hash &*&
                  true == hash_list(ks, khs, hsh) &*&
                  start == loop_fp(hsh(k), capacity) &*&
                  ks == buckets_get_keys_fp(buckets) &*&
                  buckets != nil &*&
                  true == up_to(nat_of_int(i),
                                (byLoopNthProp)(ks, (neq)(some(k)),
                                                capacity, start));
    @*/
    //@ decreases capacity - i;
  {
    //@ pred_mapping_same_len(bbs, ks);
    int index = loop(start + i, capacity);
    int bb = busybits[index];
    int kh = k_hashes[index];
    int chn = chns[index];
    void* kp = keyps[index];
    if (bb != 0 && kh == key_hash) {
      //@ close pred_mapping(nil, nil, kpr, nil);
      //@ extract_pred_for_key(nil, nil, nil, index, bbs, ks);
      //@ append_nil(reverse(take(index, kps)));
      //@ append_nil(reverse(take(index, bbs)));
      //@ append_nil(reverse(take(index, ks)));
      if (eq(kp, keyp)) {
        /*@ recover_pred_mapping(kps, bbs, ks, index); @*/
        //@ hmap_find_this_key(hm, index, k);
        //@ close hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm);
        //@ close buckets_ks_insync(chns, capacity, buckets, hsh, ks);
        return index;
      }
      //@ recover_pred_mapping(kps, bbs, ks, index);
    } else {
      //@ if (bb != 0) no_hash_no_key(ks, khs, k, index, hsh);
      //@ if (bb == 0) no_bb_no_key(ks, bbs, index);
      if (chn == 0) {
        //@ assert length(chnlist) == capacity;
        //@ buckets_keys_chns_same_len(buckets);
        //@ assert length(buckets) == capacity;
        //@ no_crossing_chains_here(buckets, index);
        //@ assert nil == get_crossing_chains_fp(buckets, index);
        //@ key_is_contained_in_the_bucket(buckets, capacity, hsh, k);
        //@ assert true == up_to(nat_of_int(i), (byLoopNthProp)(ks, (neq)(some(k)), capacity, start));
        //@ assert true == up_to(nat_of_int(i), (byLoopNthProp)(ks, (neq)(some(k)), capacity, loop_fp(hsh(k), capacity)));
        //@ assert true == up_to(succ(nat_of_int(i)), (byLoopNthProp)(ks, (neq)(some(k)), capacity, loop_fp(hsh(k), capacity)));
        //@ assert true == up_to(nat_of_int(i+1), (byLoopNthProp)(ks, (neq)(some(k)), capacity, loop_fp(hsh(k), capacity)));
        //@ assert buckets != nil;
        //@ chains_depleted_no_hope(buckets, i, loop_fp(hsh(k), capacity), k, capacity, hsh);
        //@ assert false == hmap_exists_key_fp(hm, k);
        //@ close hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm);
        //@ close buckets_ks_insync(chns, capacity, buckets, hsh, ks);
        return -1;
      }
      //@ assert(length(ks) == capacity);
    }
    //@ assert(nth(index, ks) != some(k));
    //@ assert(true == neq(some(k), nth(index, ks)));
    //@ assert(true == neq(some(k), nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, (neq)(some(k)), start, capacity, nat_of_int(capacity));
  //@ no_key_found(ks, k);
  //@ close buckets_ks_insync(chns, capacity, buckets, hsh, ks);
  //@ close hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm);
  return -1;
}

/*@
  lemma void pred_mapping_drop_key<kt>(list<void*> kps, list<int> bbs,
                                       list<option<kt> > ks, int index)
  requires pred_mapping(kps, bbs, ?keyp, ks) &*&
           0 <= index &*& index < length(bbs) &*&
           nth(index, ks) == some(?k);
  ensures pred_mapping(kps, update(index, 0, bbs), keyp, update(index, none, ks)) &*&
          [0.5]keyp(nth(index, kps), k);
  {
    open pred_mapping(kps, bbs, keyp, ks);
    switch(bbs) {
      case nil:
      case cons(h,t):
        if (index != 0) {
          pred_mapping_drop_key(tail(kps), t, tail(ks), index - 1);
        }
    }
    close pred_mapping(kps, update(index, 0, bbs), keyp, update(index, none, ks));
  }//took 5m
  @*/

/*@
  lemma void
  buckets_remove_key_chains_still_start_on_hash_rec<kt>
    (list<bucket<kt> > buckets, int capacity, kt k,
     fixpoint (kt,int) hash, int start)
  requires true == key_chains_start_on_hash_fp(buckets, start, capacity, hash);
  ensures true == key_chains_start_on_hash_fp
                    (buckets_remove_key_fp(buckets, k), start, capacity, hash);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          forall_filter((has_given_hash_fp)(hash, start, capacity),
                        (not_this_key_pair_fp)(k),
                        chains);
          buckets_remove_key_chains_still_start_on_hash_rec
            (t, capacity, k, hash, start+1);
        }
    }
  }

  lemma void
  buckets_remove_key_chains_still_start_on_hash<kt>
    (list<bucket<kt> > buckets, int capacity, kt k,
     fixpoint (kt,int) hash)
  requires true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash);
  ensures true == key_chains_start_on_hash_fp
                    (buckets_remove_key_fp(buckets, k), 0, capacity, hash);
  {
    buckets_remove_key_chains_still_start_on_hash_rec
      (buckets, capacity, k, hash, 0);
  } //took 10m
  @*/

static
int find_key_remove_chain/*@ <kt> @*/(int* busybits, void** keyps,
                                      int* k_hashes, int* chns,
                                      void* keyp, map_keys_equality* eq,
                                      int key_hash,
                                      int capacity,
                                      void** keyp_out)
/*@ requires hmapping<kt>(?kpr, ?hsh, capacity, busybits, ?kps, k_hashes, ?hm) &*&
             buckets_ks_insync(chns, capacity, ?buckets, hsh, hmap_ks_fp(hm)) &*&
             pointers(keyps, capacity, kps) &*&
             [?kfr]kpr(keyp, ?k) &*&
             hsh(k) == key_hash &*&
             [?f]is_map_keys_equality<kt>(eq, kpr) &*&
             true == hmap_exists_key_fp(hm, k)
             &*& *keyp_out |-> _; @*/
/*@ ensures hmapping<kt>(kpr, hsh, capacity,
                         busybits, kps, k_hashes,
                         hmap_rem_key_fp(hm, hmap_find_key_fp(hm, k))) &*&
            buckets_ks_insync(chns, capacity,
                                buckets_remove_key_fp(buckets, k), hsh,
                                hmap_ks_fp(hmap_rem_key_fp
                                             (hm, hmap_find_key_fp(hm, k)))) &*&
            pointers(keyps, capacity, kps) &*&
            [kfr]kpr(keyp, k) &*&
            [f]is_map_keys_equality<kt>(eq, kpr) &*&
            result == hmap_find_key_fp(hm, k) &*&
            *keyp_out |-> ?ptr &*&
            ptr == nth(result, kps) &*&
            [0.5]kpr(ptr, k); @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ open buckets_ks_insync(chns, capacity, buckets, hsh, hmap_ks_fp(hm));
  //@ assert ints(chns, capacity, ?chnlist);
  //@ assert pred_mapping(kps, ?bbs, kpr, ?ks);
  //@ assert hm == hmap(ks, ?khs);
  int i = 0;
  int start = loop(key_hash, capacity);
  //@ buckets_keys_chns_same_len(buckets);
  //@ assert true == hmap_exists_key_fp(hm, k);
  //@ assert start == loop_fp(hsh(k), capacity);
  //@ key_is_contained_in_the_bucket(buckets, capacity, hsh, k);
  //@ buckets_remove_add_one_chain(buckets, start, k);
  //@ loop_bijection(start, capacity);
  for (; i < capacity; ++i)
    /*@ invariant pred_mapping(kps, bbs, kpr, ks) &*&
                  ints(busybits, capacity, bbs) &*&
                  ints(k_hashes, capacity, khs) &*&
                  ints(chns, capacity, chnlist) &*&
                  pointers(keyps, capacity, kps) &*&
                  0 <= i &*& i <= capacity &*&
                  [f]is_map_keys_equality<kt>(eq, kpr) &*&
                  [kfr]kpr(keyp, k) &*&
                  hsh(k) == key_hash &*&
                  true == hash_list(ks, khs, hsh) &*&
                  *keyp_out |-> _ &*&
                  ks == buckets_get_keys_fp(buckets) &*&
                  i <= buckets_get_chain_fp(buckets, k, start) &*&
                  chnlist ==
                    add_partial_chain_fp
                      (loop_fp(start + i, capacity),
                       buckets_get_chain_fp(buckets, k, start) - i,
                       buckets_get_chns_fp(buckets_remove_key_fp(buckets,
                                                                 k))) &*&
                  true == up_to(nat_of_int(i),
                                (byLoopNthProp)(ks, (neq)(some(k)),
                                                capacity, start));
    @*/
    //@ decreases capacity - i;
  {
    //@ pred_mapping_same_len(bbs, ks);
    int index = loop(start + i, capacity);
    int bb = busybits[index];
    int kh = k_hashes[index];
    int chn = chns[index];
    void* kp = keyps[index];
    if (bb != 0 && kh == key_hash) {
      //@ close pred_mapping(nil, nil, kpr, nil);
      //@ extract_pred_for_key(nil, nil, nil, index, bbs, ks);
      //@ append_nil(reverse(take(index, kps)));
      //@ append_nil(reverse(take(index, bbs)));
      //@ append_nil(reverse(take(index, ks)));
      if (eq(kp, keyp)) {
        /*@ recover_pred_mapping(kps, bbs, ks, index); @*/
        //@ hmap_find_this_key(hm, index, k);
        busybits[index] = 0;
        *keyp_out = keyps[index];
        //@ hmap_rem_preserves_no_dups(ks, index);
        //@ hmap_rem_preserves_hash_list(ks, khs, hsh, index);
        //@ pred_mapping_drop_key(kps, bbs, ks, index);
        /*@ close hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes,
                               hmap_rem_key_fp(hm, hmap_find_key_fp(hm, k)));
          @*/
        //@ assert nth(index, hmap_ks_fp(hm)) == some(k);
        //@ chns_after_partial_chain_ended(buckets, k, start, i, capacity);
        //@ buckets_remove_key_still_ok(buckets, k);
        //@ buckets_rm_key_get_keys(buckets, k);
        /*@ buckets_remove_key_chains_still_start_on_hash
              (buckets, capacity, k, hsh);
          @*/
        /*@ close buckets_ks_insync(chns, capacity,
                                      buckets_remove_key_fp(buckets, k),
                                      hsh,
                                      update(index_of(some(k), ks), none, ks));
          @*/
        return index;
      }
      //@ recover_pred_mapping(kps, bbs, ks, index);
    } else {
      //@ assert(length(ks) == capacity);
      //@ if (bb != 0) no_hash_no_key(ks, khs, k, index, hsh);
      //@ if (bb == 0) no_bb_no_key(ks, bbs, index);
    }
    //@ buckets_remove_key_same_len(buckets, k);
    //@ buckets_keys_chns_same_len(buckets_remove_key_fp(buckets, k));
    //@ assert nth(index, ks) != some(k);
    //@ buckets_get_chain_longer(buckets, start, i, k, capacity);
    //@ assert buckets_get_chain_fp(buckets, k, start) != i;
    //@ buckets_get_chns_nonneg(buckets_remove_key_fp(buckets, k));
    /*@ add_part_chn_gt0(index, buckets_get_chain_fp(buckets, k, start) - i,
                         buckets_get_chns_fp
                           (buckets_remove_key_fp(buckets, k))); @*/
    //@ assert 0 < nth(index, chnlist);
    //@ assert 0 < chn;
    //@ integer_limits(&chn);
    chns[index] = chn - 1;
    //@ assert(nth(index, ks) != some(k));
    //@ assert(true == neq(some(k), nth(index, ks)));
    //@ assert(true == neq(some(k), nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
    //@ buckets_keys_chns_same_len(buckets);
    //@ assert length(buckets) == capacity;
    //@ assert length(chnlist) == length(buckets);
    //@ buckets_remove_key_same_len(buckets, k);
    //@ buckets_keys_chns_same_len(buckets_remove_key_fp(buckets, k));
    /*@ add_partial_chain_same_len
          (start + i, buckets_get_chain_fp(buckets, k, start) - i,
           buckets_get_chns_fp(buckets_remove_key_fp(buckets, k)));
      @*/
    //@ loop_fixp(start + i, capacity);
    //@ buckets_ok_get_chain_bounded(buckets, k, start);
    /*@ remove_one_cell_from_partial_chain
          (chnlist, loop_fp(start + i, capacity),
           buckets_get_chain_fp(buckets, k, start) - i,
           buckets_get_chns_fp(buckets_remove_key_fp(buckets, k)),
           capacity);
      @*/
    /*@ assert ints(chns, capacity,
      update(index, nth(index, chnlist) - 1,
      add_partial_chain_fp
      (loop_fp(start + i, capacity),
      buckets_get_chain_fp(buckets, k, start) - i,
      buckets_get_chns_fp(buckets_remove_key_fp(buckets, k)))));
      @*/
    /*@ assert ints(chns, capacity,
      add_partial_chain_fp
      (loop_fp(loop_fp(start + i, capacity) + 1, capacity),
      buckets_get_chain_fp(buckets, k, start) - i - 1,
      buckets_get_chns_fp(buckets_remove_key_fp(buckets, k))));
      @*/
    //@ inc_modulo_loop(start + i, capacity);
    //@ assert true == (loop_fp(loop_fp(start + i, capacity) + 1, capacity) == loop_fp(start + i + 1, capacity));
    /*@ chnlist = add_partial_chain_fp
                   (loop_fp(start + i + 1, capacity),
                    buckets_get_chain_fp(buckets, k, start) - i - 1,
                    buckets_get_chns_fp(buckets_remove_key_fp(buckets,
                                                              k)));
                                                              @*/
    /*@ assert ints(chns, capacity,
        add_partial_chain_fp
          (loop_fp(start + i + 1, capacity),
           buckets_get_chain_fp(buckets, k, start) - i - 1,
           buckets_get_chns_fp(buckets_remove_key_fp(buckets, k))));
           @*/
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, (neq)(some(k)), start, capacity, nat_of_int(capacity));
  //@ no_key_found(ks, k);
  //@ close hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm);

  //@ assert false;
  return -1;
}

/*@
  lemma void ks_size_limits<kt>(list<option<kt> > ks)
  requires true;
  ensures 0 <= ks_size_fp(ks) &*& ks_size_fp(ks) <= length(ks);
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        ks_size_limits(t);
    }
  }

  lemma void zero_bbs_is_for_empty<kt>(list<int> bbs,
                                       list<option<kt> > ks, int i)
  requires pred_mapping(?kps, bbs, ?kpr, ks) &*& nth(i, bbs) == 0 &*&
           0 <= i &*& i < length(bbs);
  ensures pred_mapping(kps, bbs, kpr, ks) &*& nth(i, ks) == none &*&
          ks_size_fp(ks) < length(ks);
  {
    open pred_mapping(kps, bbs, kpr, ks);
    switch(bbs) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
          assert(head(ks) == none);
          ks_size_limits(tail(ks));
        } else {
          nth_cons(i, t, h);
          zero_bbs_is_for_empty(t, tail(ks), i-1);
        }
    }
    close pred_mapping(kps, bbs, kpr, ks);
  }

  fixpoint bool cell_busy<kt>(option<kt> x) { return x != none; }

  lemma void bb_nonzero_cell_busy<kt>(list<int> bbs, list<option<kt> > ks, int i)
  requires pred_mapping(?kps, bbs, ?kp, ks) &*& nth(i, bbs) != 0 &*&
           0 <= i &*& i < length(bbs);
  ensures pred_mapping(kps, bbs, kp, ks) &*& true == cell_busy(nth(i, ks));
  {
    open pred_mapping(kps, bbs, kp, ks);
    switch(bbs) {
      case nil: break;
      case cons(h,t):
      if (i == 0) {
      } else {
        nth_cons(i, t, h);
        bb_nonzero_cell_busy(t, tail(ks), i-1);
      }
    }
    close pred_mapping(kps, bbs, kp, ks);
  }

  lemma void full_size<kt>(list<option<kt> > ks)
  requires true == up_to(nat_of_int(length(ks)), (nthProp)(ks, cell_busy));
  ensures ks_size_fp(ks) == length(ks);
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        up_to_nth_uncons(h, t, nat_of_int(length(t)), cell_busy);
        full_size(t);
    }
  }
  @*/

/*@
  predicate buckets_ks_insync_Xchain<kt>(int* chns, int capacity,
                                         list<bucket<kt> > buckets,
                                         fixpoint (kt,int) hash,
                                         int start, int fin;
                                         list<option<kt> > ks) =
    ints(chns, capacity,
         add_partial_chain_fp(start,
                              (fin < start) ? capacity + fin - start :
                                              fin - start,
                              buckets_get_chns_fp(buckets))) &*&
    true == buckets_ok(buckets) &*&
    true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash) &*&
    ks == buckets_get_keys_fp(buckets);
  @*/

/*@
  lemma void start_Xchain<kt>(int* chns, int capacity,
                              list<bucket<kt> > buckets,
                              list<option<kt> > ks,
                              fixpoint (kt,int) hsh,
                              int start)
  requires buckets_ks_insync(chns, capacity, buckets, hsh, ks) &*&
           0 <= start &*& start < capacity;
  ensures buckets_ks_insync_Xchain(chns, capacity, buckets, hsh,
                                   start, start, ks);
  {
    buckets_keys_chns_same_len(buckets);
    open buckets_ks_insync(chns, capacity, buckets, hsh, ks);
    add_part_chn_zero_len(buckets_get_chns_fp(buckets), start);
    close buckets_ks_insync_Xchain(chns, capacity, buckets, hsh, start, start, ks);
  }//took 5m
  @*/


/*@
lemma void chains_depleted_no_hope<kt>(list<bucket<kt> > buckets,
                                       int i,
                                       int start,
                                       kt k,
                                       int capacity,
                                       fixpoint (kt,int) hash)
requires buckets != nil &*&
         true == up_to(nat_of_int(i + 1),
                       (byLoopNthProp)(buckets_get_keys_fp(buckets),
                                       (neq)(some(k)),
                                       capacity,
                                       start)) &*&
         true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash) &*&
         true == buckets_ok(buckets) &*&
         0 <= i &*& i < capacity &*&
         0 <= start &*&
         start < capacity &*&
         capacity == length(buckets) &*&
         nth(loop_fp(start + i, capacity), buckets_get_chns_fp(buckets)) == 0;
ensures false == bucket_has_key_fp(k, nth(start, buckets));
{
  if (bucket_has_key_fp(k, nth(start, buckets))) {
    crossing_chains_keep_key(buckets, i, start, capacity, k);
    assert true == mem(k, map(fst, get_crossing_chains_fp(buckets, loop_fp(start + i, capacity))));
    loop_lims(start + i, capacity);
    no_crossing_chains_here(buckets, loop_fp(start + i, capacity));

    assert get_crossing_chains_fp(buckets, loop_fp(start + i, capacity)) == nil;
  }
}

@*/

static
int find_empty/*@ <kt> @*/(int* busybits, int* chns, int start, int capacity)
/*@ requires hmapping<kt>(?kp, ?hsh, capacity, busybits, ?kps, ?k_hashes, ?hm) &*&
             buckets_ks_insync(chns, capacity, ?buckets, hsh, hmap_ks_fp(hm)) &*&
             pointers(?keyps, capacity, kps) &*&
             0 <= start &*& start < capacity &*&
             hmap_size_fp(hm) < capacity; @*/
/*@ ensures hmapping<kt>(kp, hsh, capacity, busybits, kps, k_hashes, hm) &*&
            buckets_ks_insync_Xchain(chns, capacity, buckets, hsh,
                                     start, result, hmap_ks_fp(hm)) &*&
            pointers(keyps, capacity, kps) &*&
            true == hmap_empty_cell_fp(hm, result) &*&
            0 <= result &*& result < capacity; @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ assert pred_mapping(kps, ?bbs, kp, ?ks);
  //@ assert hm == hmap(ks, ?khs);
  //@ start_Xchain(chns, capacity, buckets, ks, hsh, start);
  //@ loop_bijection(start, capacity);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant pred_mapping(kps, bbs, kp, ks) &*&
                  ints(busybits, capacity, bbs) &*&
                  ints(k_hashes, capacity, khs) &*&
                  pointers(keyps, capacity, kps) &*&
                  0 <= i &*& i <= capacity &*&
                  true == up_to(nat_of_int(i),
                                (byLoopNthProp)(ks, cell_busy,
                                                capacity, start)) &*&
                  buckets_ks_insync_Xchain(chns, capacity, buckets, hsh,
                                           start, loop_fp(start + i, capacity),
                                           ks);
      @*/
    //@ decreases capacity - i;
  {
    //@ pred_mapping_same_len(bbs, ks);
    int index = loop(start + i, capacity);
    /*@ open buckets_ks_insync_Xchain(chns, capacity, buckets, hsh,
                                      start, index, ks);
      @*/
    //@ assert ints(chns, capacity, ?chnlist);
    int bb = busybits[index];
    if (0 == bb) {
      //@ zero_bbs_is_for_empty(bbs, ks, index);
      //@ close hmapping<kt>(kp, hsh, capacity, busybits, kps, k_hashes, hm);
      /*@ close buckets_ks_insync_Xchain(chns, capacity, buckets, hsh,
                                         start, index, ks);
        @*/
      return index;
    }
    int chn = chns[index];
    
    //@ buckets_keys_chns_same_len(buckets);
    //@ buckets_ok_chn_bound(buckets, index);
    /*@ outside_part_chn_no_effect(buckets_get_chns_fp(buckets), start,
                                   index, capacity);
      @*/
    //@ assert chn <= capacity;
    //@ assert capacity < INT_MAX;
    chns[index] = chn + 1;
    //@ bb_nonzero_cell_busy(bbs, ks, index);
    //@ assert(true == cell_busy(nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
    /*@ Xchain_add_one(chnlist, buckets_get_chns_fp(buckets), start,
                       index < start ? capacity + index - start : index - start,
                       capacity);
      @*/
    /*@
      if (i + 1 == capacity) {
        by_loop_for_all(ks, cell_busy, start, capacity, nat_of_int(capacity));
        full_size(ks);
        assert(false);
      }
      @*/
    /*@
      if (index < start) {
        if (start + i < capacity) loop_bijection(start + i, capacity);
        loop_injection_n(start + i + 1 - capacity, capacity, 1);
        loop_bijection(start + i + 1 - capacity, capacity);
        loop_injection_n(start + i - capacity, capacity, 1);
        loop_bijection(start + i - capacity, capacity);
      } else {
        if (capacity <= start + i) {
          loop_injection_n(start + i - capacity, capacity, 1);
          loop_bijection(start + i - capacity, capacity);
        }
        loop_bijection(start + i, capacity);
        if (start + i + 1 == capacity) {
          loop_injection_n(start + i + 1 - capacity, capacity, 1);
          loop_bijection(start + i + 1 - capacity, capacity);
        } else {
          loop_bijection(start + i + 1, capacity);
        }
      }
      @*/
    /*@
        close buckets_ks_insync_Xchain(chns, capacity, buckets, hsh,
                                       start, loop_fp(start+i+1, capacity),
                                       ks);
      @*/
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, cell_busy, start, capacity, nat_of_int(capacity));
  //@ full_size(ks);
  //@ close hmapping<kt>(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  return -1;
}

/*@

  fixpoint list<int> zero_list_fp(nat len) {
    return repeat_n<int>(len, 0);
  }

  fixpoint list<option<kt> > none_list_fp<kt>(nat len) {
    return repeat_n<option<kt> >(len, none);
  }

  lemma void move_int(int* data, int i, int len)
  requires ints(data, i, ?l1) &*& ints(data + i, len - i, ?l2) &*&
           i < len;
  ensures ints(data, i + 1, append(l1,cons(head(l2),nil))) &*&
          ints(data + i + 1, len - i - 1, tail(l2));
  {
    open(ints(data, i, l1));
    switch(l1) {
      case nil:
        open(ints(data, len-i, l2));
        close(ints(data, 1, cons(head(l2),nil)));
      case cons(h,t):
        move_int(data+1, i-1, len-1);
    }
    close(ints(data, i+1, append(l1, cons(head(l2),nil))));
  }

  lemma void extend_zero_list(nat len, int extra)
  requires true;
  ensures update(int_of_nat(len), 0,
                 append(zero_list_fp(len), cons(extra,nil))) ==
          zero_list_fp(succ(len));
  {
    switch(len) {
      case zero: return;
      case succ(l):
        extend_zero_list(l, extra);
    }
  }

  fixpoint hmap<kt> empty_hmap_fp<kt>(int capacity, list<int> hashes) {
    return hmap(none_list_fp<kt>(nat_of_int(capacity)),
                hashes);
  }

  lemma void nat_len_of_non_nil<t>(t h, list<t> t)
  requires true;
  ensures nat_of_int(length(cons(h, t)) - 1) == nat_of_int(length(t)) &*&
          nat_of_int(length(cons(h, t))) == succ(nat_of_int(length(t)));
  {
    int l = length(cons(h,t));
    assert(0 < l);
    switch(nat_of_int(l)) {
      case zero:
        note(int_of_nat(zero) == l);
        assert(false);
        return;
      case succ(lll):
        assert(nat_of_int(l) == succ(lll));
        assert(nat_of_int(int_of_nat(lll) + 1) == succ(nat_of_int(int_of_nat(lll))));
        assert(nat_of_int(int_of_nat(lll) + 1) == nat_of_int(l));
        assert(int_of_nat(nat_of_int(int_of_nat(lll) + 1)) == int_of_nat(nat_of_int(l)));
        assert(int_of_nat(lll) + 1 == l);
        assert(nat_of_int(int_of_nat(lll)) == nat_of_int(l-1));
        assert(lll == nat_of_int(l-1));
        return;
    }
  }

  lemma void produce_pred_mapping<kt>(list<int> hashes,
                                      predicate (void*; kt) kp,
                                      list<void*> pts)
  requires length(hashes) == length(pts);
  ensures pred_mapping(pts, zero_list_fp(nat_of_int(length(pts))),
                       kp, none_list_fp<kt>(nat_of_int(length(pts))));
  {
    switch(pts) {
      case nil:
        close pred_mapping(pts, zero_list_fp(nat_of_int(length(pts))),
                           kp, none_list_fp<kt>(nat_of_int(length(pts))));
        return;
      case cons(pth,ptt):
        switch(hashes) {
          case nil: break;
          case cons(hh,ht): break;
        }
        assert(hashes != nil);
        produce_pred_mapping(tail(hashes), kp, ptt);
        nat_len_of_non_nil(pth,ptt);
        close pred_mapping(pts, zero_list_fp(nat_of_int(length(pts))),
                           kp, none_list_fp<kt>(nat_of_int(length(pts))));
        return;
    }
  }

  lemma void confirm_no_dups_on_nones<kt>(nat len)
  requires true;
  ensures true == opt_no_dups(none_list_fp(len));
  {
    switch(len) {
      case zero:
        return;
      case succ(l): confirm_no_dups_on_nones(l);
    }
  }

  lemma void confirm_hash_list_for_nones<kt>(list<int> hashes,
                                             fixpoint (kt,int) hash)
  requires true;
  ensures true == hash_list(none_list_fp(nat_of_int(length(hashes))),
                            hashes, hash);
  {
    switch(hashes) {
      case nil:
        return;
      case cons(h,t):
        confirm_hash_list_for_nones(t, hash);
        nat_len_of_non_nil(h,t);
        assert(tail(none_list_fp(nat_of_int(length(hashes)))) ==
               none_list_fp(nat_of_int(length(t))));
        return;
    }
  }
  @*/

/*@
  predicate key_vals<kt,vt>(list<option<kt> > key_arr, list<vt> val_arr,
                            list<pair<kt,vt> > kvs) =
      switch (key_arr) {
        case nil: return val_arr == nil &*& kvs == nil;
        case cons(key,tail):
          return switch(key) {
            case none: return val_arr != nil &*&
                              key_vals(tail, tail(val_arr), kvs);
            case some(k): return
              val_arr != nil &*&
              true == mem(pair(k,head(val_arr)), kvs) &*&
              key_vals(tail, tail(val_arr), remove(pair(k,head(val_arr)), kvs));
          };
      };

  fixpoint bool rec_props<kt>(fixpoint (kt,int,bool) prop,
                              list<pair<kt,int> > recs) {
    switch (recs) {
      case nil: return true;
      case cons(rec,tail):
        return true == prop(fst(rec),snd(rec)) &&
                       rec_props(prop, tail);
    }
  }

  predicate mapping<kt>(list<pair<kt,int> > m,
                        list<pair<kt,void*> > addrs,
                        predicate (void*;kt) keyp,
                        fixpoint (kt,int,bool) recp,
                        fixpoint (kt,int) hash,
                        int capacity,
                        int* busybits,
                        void** keyps,
                        int* k_hashes,
                        int* chns,
                        int* values) =
     pointers(keyps, capacity, ?kps) &*&
     hmapping<kt>(keyp, hash, capacity, busybits, kps, k_hashes, ?hm) &*&
     buckets_ks_insync<kt>(chns, capacity, ?buckets, hash, ?ks) &*&
     ks == hmap_ks_fp(hm) &*&
     ints(values, capacity, ?val_arr) &*&
     true == rec_props(recp, m) &*&
     key_vals<kt,int>(hmap_ks_fp(hm), val_arr, m) &*&
     key_vals<kt,void*>(hmap_ks_fp(hm), kps, addrs);

  fixpoint bool no_dup_keys<kt,vt>(list<pair<kt,vt> > m) {
    switch(m) {
      case nil:
        return true;
      case cons(h,t):
        return (false == map_has_fp(t, fst(h))) && no_dup_keys(t);
    }
  }
  @*/

/*@
  lemma void produce_empty_key_vals<kt,vt>(list<vt> val_arr)
  requires true;
  ensures key_vals<kt,vt>(none_list_fp(nat_of_int(length(val_arr))),
                          val_arr, nil);
  {
    switch(val_arr) {
      case nil:
        close key_vals(none_list_fp(nat_of_int(length(val_arr))),
                       val_arr, nil);
        return;
      case cons(vh,vt):
        produce_empty_key_vals(vt);
        nat_len_of_non_nil(vh,vt);
        close key_vals(none_list_fp(nat_of_int(length(val_arr))),
                       val_arr, nil);
        return;
    }
  }

  @*/

/*@
  lemma void empty_keychains_start_on_hash<kt>(nat len,
                                               fixpoint (kt,int) hash,
                                               int pos, int capacity)
  requires 0 < capacity;
  ensures true == key_chains_start_on_hash_fp
                    (empty_buckets_fp<kt>(len),
                     pos, capacity, hash);
  {
    switch(len) {
      case zero:
      case succ(n):
        empty_keychains_start_on_hash(n, hash, pos + 1, capacity);
    }
  }
  @*/

/*@
  lemma void empty_buckets_hmap_insync<kt>(int* chns, int capacity,
                                           list<int> khlist,
                                           fixpoint (kt,int) hash)
  requires ints(chns, capacity, zero_list_fp(nat_of_int(capacity))) &*&
           0 < capacity;
  ensures buckets_ks_insync<kt>(chns, capacity,
                                empty_buckets_fp<kt>(nat_of_int(capacity)),
                                hash,
                                none_list_fp<kt>(nat_of_int(capacity)));
  {
    empty_buckets_chns_zeros<kt>(nat_of_int(capacity));
    empty_buckets_ok<kt>(nat_of_int(capacity));
    empty_buckets_ks_none<kt>(nat_of_int(capacity));
    empty_keychains_start_on_hash<kt>(nat_of_int(capacity), hash, 0, capacity);
  }//took 25m
  @*/

void map_impl_init/*@ <kt> @*/(int* busybits, map_keys_equality* eq,
                               void** keyps, int* khs, int* chns,
                               int* vals, int capacity)
/*@ requires map_key_type<kt>() &*& map_key_hash<kt>(?hash) &*&
             [?fr]is_map_keys_equality<kt>(eq, ?keyp) &*&
             map_record_property<kt>(?recp) &*&
             ints(busybits, capacity, ?bbs) &*&
             pointers(keyps, capacity, ?kplist) &*&
             ints(vals, capacity, ?vallist) &*&
             ints(khs, capacity, ?khlist) &*&
             ints(chns, capacity, ?chnlist) &*&
             0 < capacity &*& 2*capacity < INT_MAX; @*/
/*@ ensures mapping<kt>(empty_map_fp(), empty_map_fp(),
                        keyp, recp, hash,
                        capacity, busybits, keyps,
                        khs, chns, vals) &*&
            [fr]is_map_keys_equality<kt>(eq, keyp); @*/
{
  IGNORE(eq);
  IGNORE(keyps);
  IGNORE(khs);
  IGNORE(vals);
  //@ open map_key_type();
  //@ open map_key_hash<kt>(_);
  //@ open map_record_property(_);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant [fr]is_map_keys_equality<kt>(eq, keyp) &*&
                  ints(busybits, i, zero_list_fp(nat_of_int(i))) &*&
                  ints(busybits + i, capacity - i, drop(i,bbs)) &*&
                  pointers(keyps, capacity, kplist) &*&
                  ints(vals, capacity, vallist) &*&
                  ints(khs, capacity, khlist) &*&
                  ints(chns, i, zero_list_fp(nat_of_int(i))) &*&
                  ints(chns + i, capacity - i, drop(i, chnlist)) &*&
                  0 < capacity &*& 2*capacity < INT_MAX &*&
                  0 <= i &*& i <= capacity;
      @*/
    //@ decreases capacity - i;
  {
    //@ move_int(busybits, i, capacity);
    //@ move_int(chns, i, capacity);
    //@ extend_zero_list(nat_of_int(i), head(drop(i,bbs)));
    //@ extend_zero_list(nat_of_int(i), head(drop(i, chnlist)));
    busybits[i] = 0;
    chns[i] = 0;
    //@ assert(succ(nat_of_int(i)) == nat_of_int(i+1));
    //@ tail_drop(bbs, i);
    //@ tail_drop(chnlist, i);
  }
  //@ assert(i == capacity);
  //@ assert(drop(i,bbs) == nil);
  //@ open(ints(busybits + i, capacity - i, drop(i,bbs)));
  //@ produce_pred_mapping<kt>(khlist, keyp, kplist);
  //@ confirm_no_dups_on_nones<kt>(nat_of_int(capacity));
  //@ confirm_hash_list_for_nones(khlist, hash);
  //@ assert pointers(keyps, capacity, ?kps);
  //@ close hmapping<kt>(keyp, hash, capacity, busybits, kps, khs, empty_hmap_fp<kt>(capacity, khlist));
  //@ produce_empty_key_vals<kt,int>(vallist);
  //@ produce_empty_key_vals<kt,void*>(kplist);
  //@ empty_buckets_hmap_insync(chns, capacity, khlist, hash);
  /*@ close mapping(empty_map_fp(), empty_map_fp(), keyp, recp,
                    hash, capacity, busybits, keyps, khs, chns, vals);
    @*/
}

/*@
  lemma void ks_mem_then_map_has<kt>(list<pair<kt,int> > m, kt key, int val)
  requires true == mem(pair(key, val), m);
  ensures true == map_has_fp(m, key);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == pair(key, val)) {
        } else {
          ks_mem_then_map_has(t, key, val);
        }
    }
  }
  @*/

/*@
  lemma void map_remove_unrelated_key<kt,vt>(list<pair<kt,vt> > m,
                                             kt k1, pair<kt,vt> kv2)
  requires k1 != fst(kv2);
  ensures map_has_fp(m, k1) == map_has_fp(remove(kv2, m), k1) &*&
          map_get_fp(m, k1) == map_get_fp(remove(kv2, m), k1);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) == k1) {
        } else if (h == kv2) {
        } else {
          map_remove_unrelated_key(t, k1, kv2);
        }
    }
  }
  @*/

/*@
  lemma void kopts_has_then_keys_has<kt>(list<option<kt> > ks,
                                         list<pair<kt,int> > m, kt key)
  requires key_vals(ks, ?val_arr, m) &*& true == mem(some(key), ks);
  ensures key_vals(ks, val_arr, m) &*& true == map_has_fp(m, key);
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        open key_vals(ks, val_arr, m);
        if (h == some(key)) {
          ks_mem_then_map_has(m, key, head(val_arr));
        } else {
          if (h == none) {
            kopts_has_then_keys_has(t, m, key);
          } else {
            kopts_has_then_keys_has(t, remove(pair(get_some(h),
                                                   head(val_arr)),
                                              m),
                                    key);
            map_remove_unrelated_key(m, key, pair(get_some(h), head(val_arr)));
          }
        }
        close key_vals(ks, val_arr, m);
    }
  }

  lemma void kopts_has_not_then_keys_has_not<kt>(list<option<kt> > ks,
                                                 list<pair<kt,int> > m, kt key)
  requires key_vals(ks, ?val_arr, m) &*& false == mem(some(key), ks);
  ensures key_vals(ks, val_arr, m) &*& false == map_has_fp(m, key);
  {
    switch(ks) {
      case nil:
        open key_vals(ks, val_arr, m);
        close key_vals(ks, val_arr, m);
        return;
      case cons(h,t):
        open key_vals(ks, val_arr, m);
        if (h == some(key)) {
        } else {
          if (h == none) {
            kopts_has_not_then_keys_has_not(t, m, key);
          } else {
            kopts_has_not_then_keys_has_not(t, remove(pair(get_some(h),
                                                           head(val_arr)),
                                                      m),
                                            key);
            map_remove_unrelated_key(m, key, pair(get_some(h), head(val_arr)));
          }
        }
        close key_vals(ks, val_arr, m);
        return;
    }
  }

  lemma void hmap_exists_iff_map_has<kt>(hmap<kt> hm,
                                         list<pair<kt,int> > m, kt k)
  requires key_vals(hmap_ks_fp(hm), ?val_arr, m);
  ensures key_vals(hmap_ks_fp(hm), val_arr, m) &*&
          map_has_fp(m, k) == hmap_exists_key_fp(hm, k);
  {
    if (hmap_exists_key_fp(hm, k)) {
      kopts_has_then_keys_has(hmap_ks_fp(hm), m, k);
      assert(true == hmap_exists_key_fp(hm, k));
      assert(true == map_has_fp(m, k));
    } else {
      kopts_has_not_then_keys_has_not(hmap_ks_fp(hm), m, k);
    }
  }

  lemma void hmapping_ks_capacity<kt>(hmap<kt> hm, int capacity)
  requires hmapping<kt>(?kp, ?hsh, capacity, ?busybits, ?kps,
                        ?khs, hm);
  ensures hmapping<kt>(kp, hsh, capacity, busybits, kps,
                       khs, hm) &*&
          length(hmap_ks_fp(hm)) == capacity;
  {
    open hmapping(kp, hsh, capacity, busybits, kps, khs, hm);
    assert pred_mapping(?pts, ?bbs, kp, hmap_ks_fp(hm));
    pred_mapping_same_len(bbs, hmap_ks_fp(hm));
    close hmapping(kp, hsh, capacity, busybits, kps, khs, hm);
  }
  @*/

/*@
  lemma void remove_unique_no_dups<kt,vt>(list<pair<kt,vt> > m,
                                          pair<kt,vt> kv)
  requires false == map_has_fp(remove(kv, m), fst(kv));
  ensures no_dup_keys(m) == no_dup_keys(remove(kv, m));
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == kv) {
          assert(remove(kv, m) == t);
        } else {
          remove_unique_no_dups(t, kv);
          assert(remove(kv, m) == cons(h, remove(kv, t)));
          assert(m == cons(h,t));
          if (no_dup_keys(remove(kv,m))) {
            assert(true == no_dup_keys(t));
            assert(false == map_has_fp(remove(kv, t), fst(h)));
            map_remove_unrelated_key(t, fst(h), kv);
            assert(false == map_has_fp(t, fst(h)));
            assert(true == no_dup_keys(m));
          } else {
            if (map_has_fp(remove(kv,t),fst(h))) {
              map_remove_unrelated_key(t, fst(h), kv);
              assert(true == map_has_fp(t, fst(h)));
            } else {
              assert(false == no_dup_keys(remove(kv,t)));
            }
          }
        }
    }
  }

  lemma void hmap2map_no_key<kt,vt>(list<option<kt> > ks,
                                    list<pair<kt,vt> > m,
                                    kt key)
  requires key_vals(ks, ?va, m) &*& false == mem(some(key), ks);
  ensures key_vals(ks, va, m) &*& false == map_has_fp(m, key);
  {
    open key_vals(ks, va, m);
    switch(ks) {
      case nil:
        break;
      case cons(h,t):
        if (h == none) {
          hmap2map_no_key(t, m, key);
        } else {
          hmap2map_no_key(t, remove(pair(get_some(h), head(va)), m), key);
          map_remove_unrelated_key(m, key, pair(get_some(h), head(va)));
        }
    }
    close key_vals(ks, va, m);
  }

  lemma void map_no_dups<kt,vt>(list<option<kt> > ks, list<pair<kt,vt> > m)
  requires key_vals(ks, ?val_arr, m) &*& true == opt_no_dups(ks);
  ensures key_vals(ks, val_arr, m) &*& true == no_dup_keys(m);
  {
    open key_vals(ks, val_arr, m);
    switch(ks) {
      case nil:
        break;
      case cons(h,t):
        if (h == none) {
          map_no_dups(t, m);
        } else {
          map_no_dups(t, remove(pair(get_some(h), head(val_arr)), m));
          hmap2map_no_key(t, remove(pair(get_some(h), head(val_arr)), m),
                          get_some(h));
          remove_unique_no_dups(m, pair(get_some(h), head(val_arr)));
        }
    }
    close key_vals(ks, val_arr, m);
  }
  @*/

/*@
  lemma void map_has_this_key<kt,vt>(list<pair<kt,vt> > m, pair<kt,vt> kv)
  requires true == mem(kv, m);
  ensures true == map_has_fp(m, fst(kv));
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == kv) {
        } else {
          map_has_this_key(t, kv);
        }
    }
  }

  lemma void map_no_dups_returns_the_key<kt,vt>(list<pair<kt, vt> > m,
                                                pair<kt, vt> kv)
  requires true == mem(kv, m) &*& true == no_dup_keys(m);
  ensures map_get_fp(m, fst(kv)) == snd(kv);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == kv) {
        } else {
          map_has_this_key(t, kv);
          assert(true == map_has_fp(t, fst(kv)));
          if (fst(h) == fst(kv)) {
          }
          assert(fst(h) != fst(kv));
          map_no_dups_returns_the_key(t, kv);
        }
    }
  }
  @*/

/*@
  lemma void ks_find_returns_the_key<kt,vt>(list<option<kt> > ks,
                                            list<vt> val_arr,
                                            list<pair<kt, vt> > m, kt k)
  requires key_vals(ks, val_arr, m) &*& true == opt_no_dups(ks) &*&
           true == mem(some(k), ks);
  ensures key_vals(ks, val_arr, m) &*&
          nth(index_of(some(k), ks), val_arr) == map_get_fp(m, k);
  {
    switch(ks) {
      case nil:
        open key_vals(ks, val_arr, m);
        close key_vals(ks, val_arr, m);
      case cons(h,t):
        map_no_dups(ks, m);
        open key_vals(ks, val_arr, m);
        if (h == some(k)) {
          nth_0_head(val_arr);
          assert(index_of(some(k), ks) == 0);
          assert(nth(0, val_arr) == head(val_arr));
          assert(nth(index_of(some(k), ks), val_arr) == head(val_arr));
          assert(true == mem(pair(k,head(val_arr)), m));
          map_no_dups_returns_the_key(m, pair(k, head(val_arr)));
          assert(map_get_fp(m, k) == head(val_arr));
        } else if (h == none) {
          ks_find_returns_the_key(t, tail(val_arr), m, k);
          assert(val_arr != nil);
          mem_index_of(some(k), t);
          nth_cons(index_of(some(k), t) + 1, tail(val_arr), head(val_arr));
          cons_head_tail(val_arr);
        } else {
          ks_find_returns_the_key(t, tail(val_arr),
                                  remove(pair(get_some(h),
                                              head(val_arr)),
                                         m),
                                  k);
          map_remove_unrelated_key(m, k, pair(get_some(h), head(val_arr)));
          assert(index_of(some(k), ks) == 1 + index_of(some(k), t));

          assert(val_arr != nil);
          mem_index_of(some(k), t);
          nth_cons(index_of(some(k), t) + 1, tail(val_arr), head(val_arr));
          cons_head_tail(val_arr);
        }
        close key_vals(ks, val_arr, m);
    }
  }

  lemma void hmap_find_returns_the_key<kt,vt>(hmap<kt> hm,
                                              list<vt> val_arr,
                                              list<pair<kt, vt> > m, kt k)
  requires key_vals(hmap_ks_fp(hm), val_arr, m) &*&
           true == opt_no_dups(hmap_ks_fp(hm)) &*&
           true == hmap_exists_key_fp(hm, k);
  ensures key_vals(hmap_ks_fp(hm), val_arr, m) &*&
          nth(hmap_find_key_fp(hm, k), val_arr) == map_get_fp(m, k);
  {
    ks_find_returns_the_key(hmap_ks_fp(hm), val_arr, m, k);
  }
  @*/

/*@
  lemma void map_extract_recp<kt>(list<pair<kt,int> > m, kt k,
                                  fixpoint(kt,int,bool) prop)
  requires true == rec_props(prop, m) &*& true == map_has_fp(m, k);
  ensures true == prop(k, map_get_fp(m, k));
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) == k) {
        } else {
          map_extract_recp(t, k, prop);
        }
    }
  }
  @*/

int map_impl_get/*@ <kt> @*/(int* busybits, void** keyps,
                             int* k_hashes, int* chns,
                             int* values,
                             void* keyp, map_keys_equality* eq,
                             int hash, int* value,
                             int capacity)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, chns, values) &*&
             kp(keyp, ?k) &*&
             [?fr]is_map_keys_equality(eq, kp) &*&
             hsh(k) == hash &*&
             *value |-> ?v; @*/
/*@ ensures mapping<kt>(m, addrs, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, chns, values) &*&
            kp(keyp, k) &*&
            [fr]is_map_keys_equality(eq, kp) &*&
            (map_has_fp(m, k) ?
             (result == 1 &*&
              *value |-> ?nv &*&
              nv == map_get_fp(m, k) &*&
              true == recp(k, nv)):
             (result == 0 &*&
              *value |-> v)); @*/
{
  //@ open mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
  //@ open hmapping(kp, hsh, capacity, busybits, ?kps, k_hashes, ?hm);
  //@ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  int index = find_key(busybits, keyps, k_hashes, chns,
                       keyp, eq, hash, capacity);
  //@ hmap_exists_iff_map_has(hm, m, k);
  if (-1 == index)
  {
    //@ close mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
    return 0;
  }
  //@ hmapping_ks_capacity(hm, capacity);
  //@ assert(index < capacity);
  //@ assert(ints(values, capacity, ?val_arr));
  *value = values[index];
  //@ hmap_find_returns_the_key(hm, val_arr, m, k);
  //@ map_extract_recp(m, k, recp);
  //@ close mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
  return 1;
}


/*@
  lemma void ks_map_size<kt>(list<option<kt> > ks, list<pair<kt,int> > m)
  requires key_vals(ks, ?va, m);
  ensures key_vals(ks, va, m) &*&
          ks_size_fp(ks) == map_size_fp(m);
  {
    open key_vals(ks, va, m);
    switch(ks) {
      case nil:
      case cons(h,t):
        if (h == none) {
          ks_map_size(t, m);
        } else {
          ks_map_size(t, remove(pair(get_some(h), head(va)), m));
        }

    }
    close key_vals(ks, va, m);
  }

  lemma void hmap_map_size<kt>(hmap<kt> hm, list<pair<kt,int> > m)
  requires key_vals(hmap_ks_fp(hm), ?va, m);
  ensures key_vals(hmap_ks_fp(hm), va, m) &*&
          hmap_size_fp(hm) == map_size_fp(m);
  {
    ks_map_size(hmap_ks_fp(hm), m);
  }
  @*/

/*@
  lemma void put_keeps_pred_mapping<kt>(list<void*> pts, list<int> bbs,
                                        predicate (void*; kt) pred,
                                        list<option<kt> > ks,
                                        int index, void* kp, kt k)
  requires pred_mapping(pts, bbs, pred, ks) &*& [0.5]pred(kp, k) &*&
           0 <= index &*& index < length(bbs) &*&
           nth(index, ks) == none;
  ensures pred_mapping(update(index, kp, pts), update(index, 1, bbs),
                       pred, update(index, some(k), ks));
  {
    open pred_mapping(pts, bbs, pred, ks);
    switch(bbs) {
      case nil: break;
      case cons(bbh, bbt):
        if (index == 0) {
          tail_of_update_0(pts, kp);
          tail_of_update_0(ks, some(k));
          head_update_0(kp, pts);
        } else {
          put_keeps_pred_mapping(tail(pts), bbt, pred, tail(ks),
                                 index-1, kp, k);
          cons_head_tail(pts);
          cons_head_tail(ks);
          update_tail_tail_update(head(pts), tail(pts), index, kp);
          update_tail_tail_update(head(ks), tail(ks), index, some(k));
          update_tail_tail_update(bbh, bbt, index, 1);
        }
        update_non_nil(pts, index, kp);
        update_non_nil(ks, index, some(k));
    }
    close pred_mapping(update(index, kp, pts), update(index, 1, bbs),
                       pred, update(index, some(k), ks));
  }
  @*/

/*@
  lemma void put_preserves_no_dups<kt>(list<option<kt> > ks, int i, kt k)
  requires false == mem(some(k), ks) &*& true == opt_no_dups(ks);
  ensures true == opt_no_dups(update(i, some(k), ks));
  {
    switch(ks) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          put_preserves_no_dups(t, i-1, k);
          if (h == none) {
          } else {
            assert(false == mem(h, t));
            update_irrelevant_cell(h, i-1, some(k), t);
            assert(false == mem(h, update(i-1, some(k), t)));
          }
        }
    }
  }
  @*/

/*@
  lemma void hmap_coherent_hash_update<kt>(list<option<kt> > ks, list<int> khs,
                                           fixpoint (kt,int) hash,
                                           int index, kt nk, int nhsh)
  requires true == hash_list(ks, khs, hash) &*& hash(nk) == nhsh &*&
           0 <= index;
  ensures true == hash_list(update(index, some(nk), ks),
                            update(index, nhsh, khs), hash);
  {
    switch(ks) {
      case nil: break;
      case cons(h,t):
        update_non_nil(khs, index, nhsh);
        if (index == 0) {
          head_update_0(some(nk), ks);
          head_update_0(nhsh, khs);
          tail_of_update_0(khs, nhsh);
          assert(update(0, nhsh, khs) != nil);
          assert(true == hash_list(t, tail(update(0, nhsh, khs)), hash));
          assert(head(update(0, nhsh, khs)) == hash(get_some(head(update(0, some(nk), ks)))));
        } else {
          hmap_coherent_hash_update(t, tail(khs), hash, index-1, nk, nhsh);
          cons_head_tail(khs);
          update_tail_tail_update(head(khs), tail(khs), index, nhsh);
          update_tail_tail_update(h, t, index, some(nk));
        }
    }
  }
  @*/

/*@
  lemma void put_remove_interchangable<kt,vt>(list<pair<kt,vt> > m,
                                              pair<kt,vt> kv1,
                                              kt k2, vt v2)
  requires fst(kv1) != k2;
  ensures map_put_fp(remove(kv1, m), k2, v2) ==
          remove(kv1, (map_put_fp(m, k2, v2)));
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (h == kv1) {
        } else {
        }
    }
  }

  lemma void coherent_put_preserves_key_vals<kt,vt>(list<option<kt> > ks,
                                                    list<vt> vals,
                                                    list<pair<kt,vt> > m,
                                                    int i, kt k, vt v)
  requires key_vals(ks, vals, m) &*&
           0 <= i &*& i < length(ks) &*& nth(i, ks) == none &*&
           false == mem(some(k), ks);
  ensures key_vals(update(i, some(k), ks), update(i, v, vals),
                   map_put_fp(m, k, v));
  {
    open key_vals(ks, vals, m);
    switch(ks) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
          assert(true == mem(pair(k,v), map_put_fp(m, k, v)));
          assert(head(update(i, some(k), ks)) == some(k));
          head_update_0(v, vals);
          assert(head(update(i, v, vals)) == v);
          tail_of_update_0(vals, v);
          tail_of_update_0(ks, some(k));
          assert(remove(pair(k,v), map_put_fp(m, k, v)) == m);
        } else {
          update_tail_tail_update(head(vals), tail(vals), i, v);
          update_tail_tail_update(h, t, i, some(k));
          cons_head_tail(vals);
          if (h == none) {
            coherent_put_preserves_key_vals(t, tail(vals), m, i-1, k, v);
          } else {
            coherent_put_preserves_key_vals(t, tail(vals),
                                            remove(pair(get_some(h),
                                                        head(vals)),
                                                   m),
                                            i-1, k, v);
            assert(head(update(i, some(k), ks)) == h);
            head_update_nonzero(i, v, vals);
            assert(head(update(i, v, vals)) == head(vals));
            assert(true == mem(pair(get_some(h),head(vals)), map_put_fp(m, k, v)));

            //assert(false == mem(pair(get_some(h), head(vals)), m));
            assert(get_some(h) != k);
            put_remove_interchangable(m, pair(get_some(h), head(vals)), k, v);
            assert(map_put_fp(remove(pair(get_some(h), head(vals)), m), k, v) ==
                   remove(pair(get_some(h), head(vals)), (map_put_fp(m, k, v))));
          }
        }
        update_non_nil(vals, i, v);
    }
    close key_vals(update(i, some(k), ks), update(i, v, vals),
                   map_put_fp(m, k, v));
  }
  @*/

/*@
  lemma void
  buckets_put_chains_still_start_on_hash<kt>(list<bucket<kt> > buckets,
                                             kt k, int shift,
                                             int start, int dist,
                                             fixpoint (kt,int) hash,
                                             int capacity)
  requires true == key_chains_start_on_hash_fp(buckets, shift,
                                               capacity, hash) &*&
           loop_fp(hash(k), capacity) == start + shift &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*& dist < capacity;
  ensures true == key_chains_start_on_hash_fp
                    (buckets_put_key_fp(buckets, k,
                                        start, dist),
                     shift, capacity, hash);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          if (start == 0) {
            assert true == has_given_hash_fp(hash, shift, capacity,
                                             pair(k, nat_of_int(dist)));
          } else {
            buckets_put_chains_still_start_on_hash
              (t, k, shift + 1, start - 1, dist, hash, capacity);

          }
        }
    }
  }//took 10m
  @*/

/*@
  lemma void buckets_ks_put_key_insync<kt>(int* chns, int capacity,
                                           fixpoint (kt,int) hsh,
                                           int start,
                                           int fin,
                                           kt k,
                                           list<option<kt> > ks)
  requires buckets_ks_insync_Xchain(chns, capacity, ?buckets,
                                    hsh, start, fin, ks) &*&
           capacity == length(buckets) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= fin &*& fin < length(buckets) &*&
           false == mem(k, buckets_all_keys_fp(buckets)) &*&
           start == loop_fp(hsh(k), capacity) &*&
           nth(fin, buckets_get_keys_fp(buckets)) == none;
  ensures buckets_ks_insync(chns, capacity,
                            buckets_put_key_fp(buckets, k, start,
                                               loop_fp(capacity + fin - start,
                                                       capacity)),
                            hsh,
                            update(fin, some(k), ks));
  {
    open buckets_ks_insync_Xchain(chns, capacity, buckets,
                                  hsh, start, fin, ks);
    int dist = 0;
    if (fin == 0 && start != 0) {
      dist = capacity - start;
      loop_bijection(capacity + fin - start, capacity);
      loop_injection(0, capacity);
      loop_bijection(0, capacity);
    } else if (fin < start) {
      dist = fin + capacity - start;
      loop_bijection(fin - start + capacity, capacity);
      loop_injection_n(fin + capacity, capacity, -1);
    } else {
      dist = fin - start;
      loop_injection_n(fin - start + capacity, capacity, -1);
      loop_bijection(fin - start, capacity);
    }
    buckets_add_part_get_chns(buckets, k, start, dist);
    assert loop_fp(capacity + fin - start, capacity) == dist;
    loop_bijection(fin, capacity);
    assert loop_fp(start + dist, capacity) == fin;
    buckets_put_still_ok(buckets, k, start, dist);
    buckets_put_chains_still_start_on_hash
      (buckets, k, 0, start, dist, hsh, length(buckets));
    buckets_put_update_ks(buckets, ks, k, start, dist);
    close buckets_ks_insync(chns, capacity,
                            buckets_put_key_fp(buckets, k, start,
                                               dist),
                            hsh,
                            update(fin, some(k), ks));
  }//took 275m and counting
  @*/

void map_impl_put/*@ <kt> @*/(int* busybits, void** keyps,
                              int* k_hashes, int* chns,
                              int* values,
                              void* keyp, int hash, int value,
                              int capacity)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, chns, values) &*&
             [0.5]kp(keyp, ?k) &*& true == recp(k, value) &*&
             hsh(k) == hash &*&
             false == map_has_fp(m, k) &*&
             map_size_fp(m) < capacity; @*/
/*@ ensures true == recp(k, value) &*&
            mapping<kt>(map_put_fp(m, k, value),
                        map_put_fp(addrs, k, keyp),
                        kp, recp,
                        hsh,
                        capacity, busybits,
                        keyps, k_hashes, chns, values); @*/
{
  //@ open mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
  //@ open hmapping(kp, hsh, capacity, busybits, ?kps, k_hashes, ?hm);
  int start = loop(hash, capacity);
  //@ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  //@ hmap_map_size(hm, m);
  //@ assert buckets_ks_insync(chns, capacity, ?buckets, hsh, ?ks);
  //@ assert ks == hmap_ks_fp(hm);
  //@ open buckets_ks_insync(chns, capacity, buckets, hsh, ks);
  //@ assert ks == buckets_get_keys_fp(buckets);
  //@ buckets_keys_chns_same_len(buckets);
  //@ close buckets_ks_insync(chns, capacity, buckets, hsh, ks);
  //@ assert length(buckets) == capacity;
  int index = find_empty(busybits, chns, start, capacity);


  //@ hmapping_ks_capacity(hm, capacity);
  //@ open hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  //@ assert pred_mapping(kps, ?bbs, kp, ks);
  //@ put_keeps_pred_mapping(kps, bbs, kp, ks, index, keyp, k);
  //@ hmap_exists_iff_map_has(hm, m, k);
  //@ put_preserves_no_dups(ks, index, k);
  //@ assert(hm == hmap(ks, ?khs));
  //@ assert(ints(values, capacity, ?vals));
  //@ hmap_coherent_hash_update(ks, khs, hsh, index, k, hash);
  busybits[index] = 1;
  keyps[index] = keyp;
  k_hashes[index] = hash;
  values[index] = value;
  /*@ close hmapping(kp, hsh, capacity, busybits, update(index, keyp, kps),
                     k_hashes, hmap_put_key_fp(hm, index, k, hash));
    @*/
  //@ coherent_put_preserves_key_vals(hmap_ks_fp(hm), vals, m, index, k, value);
  //@ coherent_put_preserves_key_vals(hmap_ks_fp(hm), kps, addrs, index, k, keyp);
  // @ assert capacity == length(chns);
  //@ assert length(hmap_ks_fp(hm)) == capacity;
  //@ assert length(ks) == capacity;
  //@ assert length(ks) == length(buckets);
  //@ no_key_in_ks_no_key_in_buckets(buckets, k);
  /*@ buckets_ks_put_key_insync(chns, capacity,
                                hsh,
                                start, index, k,
                                ks);
    @*/
  /*@ close mapping(map_put_fp(m, k, value), map_put_fp(addrs, k, keyp),
                    kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
    @*/
}

/*@
  lemma void hmap_rem_preserves_pred_mapping<kt>(list<char*> kps, list<int> bbs,
                                                 predicate (void*;kt) keyp,
                                                 list<option<kt> > ks,
                                                 int i)
  requires pred_mapping(kps, bbs, keyp, ks) &*&
           0 <= i &*& i < length(ks) &*& nth(i, ks) == some(?k);
  ensures pred_mapping(kps, update(i, 0, bbs), keyp, update(i, none, ks)) &*&
          [0.5]keyp(nth(i, kps), k);
  {
    open pred_mapping(kps, bbs, keyp, ks);
    switch(bbs) {
      case nil: break;
      case cons(bbh, bbt):
        cons_head_tail(ks);
        cons_head_tail(kps);
        if (i == 0) {
        } else {
          hmap_rem_preserves_pred_mapping(tail(kps), bbt, keyp, tail(ks), i-1);
          nth_cons(i, tail(ks), head(ks));
          nth_cons(i, tail(kps), head(kps));
        }
    }
    close pred_mapping(kps, update(i, 0, bbs), keyp, update(i, none, ks));
  }
  @*/

/*@
  lemma void map_erase_preserves_rec_props<kt>(list<pair<kt,int> > m,
                                               fixpoint(kt,int,bool) recp,
                                               kt k)
  requires true == rec_props(recp, m);
  ensures true == rec_props(recp, map_erase_fp(m, k));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        if (fst(h) == k) {
        } else {
          map_erase_preserves_rec_props(t, recp, k);
        }
    }
  }
  @*/

/*@
  lemma void map_has_not_mem_not<kt,vt>(list<pair<kt,vt> > m,
                                        kt k, vt v)
  requires false == map_has_fp(m, k);
  ensures false == mem(pair(k,v), m);
  {
    switch(m){
      case nil: break;
      case cons(h,t):
        map_has_not_mem_not(t, k, v);
    }
  }

  lemma void map_no_dups_has_that_pair<kt,vt>(pair<kt,vt> mh,
                                              list<pair<kt,vt> > mt,
                                              kt k, vt v)
  requires true == no_dup_keys(cons(mh,mt)) &*&
           true == mem(pair(k,v), cons(mh,mt)) &*&
           fst(mh) == k;
  ensures mh == pair(k,v);
  {
    if (mh != pair(k,v)) {
      assert(false == map_has_fp(mt, fst(mh)));
      map_has_not_mem_not(mt, k, v);
    }
  }

  lemma void map_erase_that_key<kt,vt>(list<pair<kt,vt> > m,
                                       kt k, vt v)
  requires true == no_dup_keys(m) &*& true == mem(pair(k, v), m);
  ensures map_erase_fp(m, k) == remove(pair(k, v), m);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (fst(h) == k) {
          map_no_dups_has_that_pair(h, t, k, v);
          assert(h == pair(k,v));
        } else {
          map_erase_that_key(t, k, v);
        }
    }
  }

  lemma void map_erase_unrelated_key<kt,vt>(list<pair<kt,vt> > m,
                                             pair<kt,vt> kv1, kt k2)
  requires fst(kv1) != k2;
  ensures mem(kv1, m) == mem(kv1, map_erase_fp(m, k2)) &*&
          remove(kv1, map_erase_fp(m, k2)) == map_erase_fp(remove(kv1, m), k2);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (h == kv1) {
        } else {
          if (fst(h) == k2) {
          } else {
            map_erase_unrelated_key(t, kv1, k2);
          }
        }
    }
  }

  lemma void map_erase_remove_unrelated<kt>(list<pair<kt,int> > m,
                                            pair<kt,int> kv1, kt k2)
  requires fst(kv1) != k2;
  ensures remove(kv1, map_erase_fp(m, k2)) == map_erase_fp(remove(kv1, m), k2);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (h == kv1) {
        } else {
          if (fst(h) == k2) {
          } else {
            map_erase_remove_unrelated(t, kv1, k2);
          }
        }
    }
  }

  lemma void ks_rem_map_erase_coherent<kt,vt>(list<option<kt> > ks,
                                              list<pair<kt,vt> > m,
                                              int i, kt k)
  requires key_vals(ks, ?vals, m) &*& nth(i, ks) == some(k) &*&
           true == no_dup_keys(m) &*& true == opt_no_dups(ks) &*&
           0 <= i &*& i < length(ks);
  ensures key_vals(update(i, none, ks), vals, map_erase_fp(m, k));
  {
    switch(ks) {
      case nil:
        open key_vals(ks, vals, m);
        close key_vals(update(i, none, ks), vals, map_erase_fp(m, k));
        break;
      case cons(h,t):
        open key_vals(ks, vals, m);
        if (i == 0) {
          tail_of_update_0(ks, none);
          assert(h == some(k));
          assert(true == mem(pair(k, head(vals)), m));
          map_erase_that_key(m, k, head(vals));
          assert(map_erase_fp(m, k) == remove(pair(k, head(vals)), m));
        } else {
          if (h == none) {
            ks_rem_map_erase_coherent(t, m, i-1, k);
          } else {
            hmap2map_no_key(t, remove(pair(get_some(h), head(vals)), m),
                            get_some(h));
            remove_unique_no_dups(m, pair(get_some(h), head(vals)));
            ks_rem_map_erase_coherent(t, remove(pair(get_some(h),
                                                     head(vals)), m),
                                      i-1, k);

            map_erase_unrelated_key(m, pair(get_some(h), head(vals)), k);
            update_tail_tail_update(h, t, i, none);
          }
        }
        close key_vals(update(i, none, ks), vals, map_erase_fp(m, k));
    }
  }

  lemma void hmap_ks_hmap_rm<kt>(hmap<kt> hm, int i)
  requires true;
  ensures hmap_ks_fp(hmap_rem_key_fp(hm, i)) == update(i, none, hmap_ks_fp(hm));
  {
    switch(hm) {
      case hmap(ks, khs): break;
    }
  }

  lemma void hmap_rem_map_erase_coherent<kt,vt>(hmap<kt> hm,
                                                list<pair<kt, vt> > m,
                                                int i, kt k)
  requires key_vals(hmap_ks_fp(hm), ?vals, m) &*&
           nth(i, hmap_ks_fp(hm)) == some(k) &*&
           true == opt_no_dups(hmap_ks_fp(hm)) &*&
           0 <= i &*& i < length(hmap_ks_fp(hm));
  ensures key_vals(hmap_ks_fp(hmap_rem_key_fp(hm, i)),
                   vals, map_erase_fp(m, k));
  {
     map_no_dups(hmap_ks_fp(hm), m);
     hmap_ks_hmap_rm(hm, i);
     ks_rem_map_erase_coherent(hmap_ks_fp(hm), m, i, k);
  }
  @*/

void map_impl_erase/*@ <kt> @*/(int* busybits, void** keyps,
                                int* k_hashes, int* chns,
                                void* keyp,
                                map_keys_equality* eq, int hash, int capacity,
                                void** keyp_out)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, chns, ?values) &*&
             [0.5]kp(keyp, ?k) &*&
             [?fr]is_map_keys_equality<kt>(eq, kp) &*&
             hsh(k) == hash &*&
             *keyp_out |-> ?ko &*&
             true == map_has_fp(m, k); @*/
/*@ ensures [0.5]kp(keyp, k) &*&
            [fr]is_map_keys_equality<kt>(eq, kp) &*&
               *keyp_out |-> ?nko &*&
               nko == map_get_fp(addrs, k) &*&
               [0.5]kp(nko, k) &*&
               mapping<kt>(map_erase_fp(m, k), map_erase_fp(addrs, k),
                           kp, recp, hsh,
                           capacity, busybits, keyps, k_hashes, chns, values); @*/
{
  //@ open mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
  //@ open hmapping(kp, hsh, capacity, busybits, ?kps, k_hashes, ?hm);
  //@ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  //@ hmap_exists_iff_map_has(hm, m, k);
  find_key_remove_chain(busybits, keyps, k_hashes, chns,
                        keyp, eq, hash, capacity, keyp_out);
  //@ hmap_exists_iff_map_has(hm, m, k);
  // @ hmapping_ks_capacity(hm, capacity);
  // @ assert(index < capacity);
  // @ open hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  // @ assert(pred_mapping(kps, ?bbs, kp, ?ks));
  // @ assert(ints(k_hashes, capacity, ?khs));
  //@ hmap_find_returns_the_key(hm, kps, addrs, k);
  //@ mem_nth_index_of(some(k), hmap_ks_fp(hm));
  // @ hmap_rem_preserves_pred_mapping(kps, bbs, kp, ks, index);
  // @ hmap_rem_preserves_no_dups(ks, index);
  // @ hmap_rem_preserves_hash_list(ks, khs, hsh, index);
  // @ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hmap_rem_key_fp(hm, index));
  //@ map_erase_preserves_rec_props(m, recp, k);
  //@ hmap_rem_map_erase_coherent(hm, m, hmap_find_key_fp(hm,k), k);
  //@ hmap_rem_map_erase_coherent(hm, addrs, hmap_find_key_fp(hm,k), k);
  /*@ close mapping(map_erase_fp(m, k), map_erase_fp(addrs, k),
                    kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
    @*/
}

/*@
  fixpoint bool nonzero(int x) { return x != 0; }

  lemma void add_bit_to_nonzero_count(list<int> bbs, int i, int s)
  requires s == count(take(i, bbs), nonzero) &*& 0 <= i &*& i < length(bbs);
  ensures nth(i, bbs) == 0 ?
           s == count(take(i+1, bbs), nonzero) :
           s+1 == count(take(i+1, bbs), nonzero);
  {
    switch(bbs) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          if (h == 0) {
            add_bit_to_nonzero_count(t, i-1, s);
          } else {
            add_bit_to_nonzero_count(t, i-1, s-1);
          }
        }
    }
  }

  lemma void nonzero_count_is_ks_size<kt>(list<int> bbs, list<option<kt> > ks)
  requires pred_mapping(?kps, bbs, ?pred, ks);
  ensures pred_mapping(kps, bbs, pred, ks) &*&
          count(bbs, nonzero) == ks_size_fp(ks);
  {
    open pred_mapping(kps, bbs, pred, ks);
    switch(bbs) {
      case nil: break;
      case cons(h,t):
        nonzero_count_is_ks_size(t, tail(ks));
    }
    close pred_mapping(kps, bbs, pred, ks);
  }
  @*/

int map_impl_size/*@ <kt> @*/(int* busybits, int capacity)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh, capacity, busybits,
                         ?keyps, ?k_hashes, ?chns, ?values); @*/
/*@ ensures mapping<kt>(m, addrs, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, chns, values) &*&
            result == map_size_fp(m);@*/
{
  //@ open mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
  //@ open hmapping(kp, hsh, capacity, busybits, ?kps, k_hashes, ?hm);
  //@ assert ints(busybits, capacity, ?bbs);
  //@ assert pointers(keyps, capacity, kps);
  //@ assert ints(k_hashes, capacity, ?khs);
  //@ assert pred_mapping(kps, bbs, kp, ?ks);
  int s = 0;
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant 0 <= i &*& i <= capacity &*&
                  0 < capacity &*& 2*capacity < INT_MAX &*&
                  ints(busybits, capacity, bbs) &*&
                  pointers(keyps, capacity, kps) &*&
                  ints(k_hashes, capacity, khs) &*&
                  pred_mapping(kps, bbs, kp, ks) &*&
                  true == opt_no_dups(ks) &*&
                  true == hash_list(ks, khs, hsh) &*&
                  hm == hmap(ks, khs) &*&
                  count(take(i, bbs), nonzero) == s &*&
                  0 <= s &*& s <= i;
      @*/
    //@ decreases capacity - i;
  {
    //@ add_bit_to_nonzero_count(bbs, i, s);
    if (busybits[i] != 0)
    {
      ++s;
    }
  }
  //@ nonzero_count_is_ks_size(bbs, ks);
  //@ assert(s == hmap_size_fp(hm));
  //@ hmap_map_size(hm, m);
  //@ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  //@ close mapping(m, addrs, kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
  return s;
}

/*@
  lemma void map_get_keeps_recp<kt>(list<pair<kt,int> > m, kt k)
  requires mapping(m, ?addrs, ?kp, ?rp, ?hsh,
                   ?cap, ?bbs, ?kps, ?khs, ?chns, ?vals) &*&
           true == map_has_fp(m, k);
  ensures true == rp(k, map_get_fp(m, k)) &*&
          mapping(m, addrs, kp, rp, hsh,
                  cap, bbs, kps, khs, chns, vals);
  {
    open mapping(m, addrs, kp, rp, hsh, cap, bbs, kps, khs, chns, vals);
    map_extract_recp(m, k, rp);
    close mapping(m, addrs, kp, rp, hsh, cap, bbs, kps, khs, chns, vals);
  }
  @*/

/*@
  lemma void map_has_to_mem<kt>(list<pair<kt, int> > m, kt k)
  requires true;
  ensures map_has_fp(m, k) == mem(k, map(fst, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,value):
          if (key != k) map_has_to_mem(t, k);
        }
    }
  
  }
  @*/

/*@
  lemma void no_dup_keys_to_no_dups<kt>(list<pair<kt, int> > m)
  requires true;
  ensures no_dup_keys(m) == no_dups(map(fst, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          no_dup_keys_to_no_dups(t);
          map_has_to_mem(t, key);
        }
    }
  }
  @*/

/*@
  lemma void map_no_dup_keys<kt>(list<pair<kt, int> > m)
  requires mapping(m, ?addrs, ?kp, ?rp, ?hsh,
                   ?cap, ?bbs, ?kps, ?khs, ?chns, ?vals);
  ensures mapping(m, addrs, kp, rp, hsh,
                  cap, bbs, kps, khs, chns, vals) &*&
          true == no_dups(map(fst, m));
  {
    open mapping(m, addrs, kp, rp, hsh, cap, bbs, kps, khs, chns, vals);
    open hmapping(kp, hsh, cap, ?busybits, ?lkps, khs, ?hm);
    assert pred_mapping(lkps, ?lbbs, kp, ?ks);
    map_no_dups(ks, m);
    close hmapping(kp, hsh, cap, busybits, lkps, khs, hm);
    close mapping(m, addrs, kp, rp, hsh, cap, bbs, kps, khs, chns, vals);
    no_dup_keys_to_no_dups(m);
  }
  @*/
