#include <stdint.h>
#include <string.h>

#include "map.h"
#include "include_ignored_by_verifast.h"
#include "lib/ignore.h"

//@ #include <list.gh>
//@ #include <listex.gh>
//@ #include <nat.gh>
//@ #include "stdex.gh"
//@ #include "nth_prop.gh"
//@ #include "modulo.gh"

/*@
  inductive bucket<kt> = bucket(list<pair<kt, nat> >);
  //list<bucket<kt> > - the map.

  fixpoint list<pair<kt, nat> > advance_acc<kt>(list<pair<kt, nat> > acc) {
    switch(acc) {
      case nil: return nil;
      case cons(h,t):
        return switch(h) { case pair(key,distance):
            return switch(distance) {
            case zero: return advance_acc(t);
            case succ(n): return cons(pair(fst(h), n), advance_acc(t));
          };
        };
    }
  }

  fixpoint list<nat> get_just_tails<kt>(list<pair<kt, nat> > acc) {
    return map(snd, acc);
  }

  fixpoint option<kt> get_current_key_fp<kt>(list<pair<kt, nat> > acc) {
    switch(acc) {
      case nil: return none;
      case cons(h,t):
        return switch(h) { case pair(key,distance):
          return switch(distance) {
            case zero: return some(key);
            case succ(n): return get_current_key_fp(t);
          };
        };
    }
  }

  fixpoint list<pair<kt, nat> > acc_at_this_bucket<kt>(list<pair<kt, nat> > acc,
                                                       bucket<kt> next_bucket) {
    switch(next_bucket) { case bucket(tails): return append(acc, tails);}
  }

  fixpoint list<pair<kt, nat> >
  get_wraparound<kt>(list<pair<kt, nat> > acc,
                     list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil: return acc;
      case cons(h,t):
        return get_wraparound(advance_acc(acc_at_this_bucket(acc, h)), t);
    }
  }

  fixpoint bool upper_limit<kt>(int lim, pair<kt,nat> x) {
    return int_of_nat(snd(x)) < lim;
  }

  fixpoint bool buckets_ok_rec<kt>(list<pair<kt, nat> > acc,
                                   list<bucket<kt> > buckets,
                                   int bound) {
    switch(buckets) {
      case nil:
        return distinct(get_just_tails(acc)) &&
               forall(acc, (upper_limit)(bound));
      case cons(bkh,bkt):
        return distinct(get_just_tails(acc_at_this_bucket(acc, bkh))) &&
               forall(acc_at_this_bucket(acc, bkh), (upper_limit)(bound)) &&
               buckets_ok_rec(advance_acc(acc_at_this_bucket(acc, bkh)),
                              bkt, bound);
    }
  }

  fixpoint bool not_this_key_pair_fp<kt>(kt k, pair<kt, nat> p) {
    return fst(p) != k;
  }

  fixpoint list<bucket<kt> >
  buckets_remove_key_fp<kt>(list<bucket<kt> > buckets, kt k) {
    switch(buckets) {
      case nil: return nil;
      case cons(bh,bt):
        return switch(bh) { case bucket(chains):
          return cons(bucket(filter((not_this_key_pair_fp)(k), chains)),
                      buckets_remove_key_fp(bt, k));
        };
    }
  }

  fixpoint bool buckets_ok<kt>(list<bucket<kt> > buckets) {
    return buckets_ok_rec(get_wraparound(nil, buckets), buckets, length(buckets));
  }

  fixpoint list<int> buckets_get_chns_rec_fp<kt>(list<pair<kt, nat> > acc,
                                                 list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil: return nil;
      case cons(bh,bt):
        return cons(length(acc_at_this_bucket(acc, bh)),
                    buckets_get_chns_rec_fp(advance_acc
                                              (acc_at_this_bucket(acc, bh)),
                                            bt));
    }
  }

  fixpoint list<int> buckets_get_chns_fp<kt>(list<bucket<kt> > buckets) {
    return buckets_get_chns_rec_fp(get_wraparound(nil, buckets), buckets);
  }

  fixpoint list<option<kt> >
  buckets_get_keys_rec_fp<kt>(list<pair<kt, nat> > acc,
                              list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil: return nil;
      case cons(bh,bt):
        return cons(get_current_key_fp(acc_at_this_bucket(acc, bh)),
                    buckets_get_keys_rec_fp(advance_acc
                                              (acc_at_this_bucket(acc, bh)),
                                            bt));
    }
  }

  fixpoint list<option<kt> > buckets_get_keys_fp<kt>(list<bucket<kt> > buckets) {
    return buckets_get_keys_rec_fp(get_wraparound(nil, buckets), buckets);
  }

  fixpoint int get_optional_hash_fp<kt>(fixpoint (kt,int) hash, option<kt> k) {
    switch(k) {
      case none: return 0;
      case some(key): return hash(key);
    }
  }

  fixpoint list<int> get_keys_hashes_fp<kt>(list<option<kt> > keys,
                                            fixpoint (kt,int) hash) {
    return map((get_optional_hash_fp)(hash), keys);
  }

  @*/

/*@
  lemma void buckets_ok_acc_bounded_rec<kt>(list<pair<kt, nat> > acc,
                                            list<bucket<kt> > buckets,
                                            int bound)
  requires true == buckets_ok_rec(acc, buckets, bound);
  ensures true == forall(get_wraparound(acc, buckets), (upper_limit)(bound));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_ok_acc_bounded_rec(advance_acc(acc_at_this_bucket(acc, h)),
                                   t, bound);
    }
  }

  lemma void advance_chain_contains<kt>(kt key, nat prev_tail,
                                        list<pair<kt, nat> > acc2)
  requires true == contains(acc2, pair(key, succ(prev_tail)));
  ensures true == contains(advance_acc(acc2), pair(key, prev_tail));
  {
    switch(acc2) {
      case nil:
      case cons(h,t):
        if (h == pair(key, succ(prev_tail))) {
        } else {
          advance_chain_contains(key, prev_tail, t);
          switch(h) { case pair(k,d):
            switch(d) {
              case zero:
              case succ(n):
            }
          }
        }
    }
  }

  lemma void advance_acc_subset<kt>(list<pair<kt, nat> > acc1,
                                    list<pair<kt, nat> > acc2)
  requires true == subset(acc1, acc2);
  ensures true == subset(advance_acc(acc1), advance_acc(acc2));
  {
    switch(acc1) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(k, dist):
          switch(dist) {
            case zero:
            case succ(prev_dist):
              advance_chain_contains(k, prev_dist, acc2);
          }
        }
        advance_acc_subset(t, acc2);
    }
  }

  lemma void acc_at_this_bucket_subset<kt>(list<pair<kt, nat> > acc1,
                                           list<pair<kt, nat> > acc2,
                                           bucket<kt> b)
  requires true == subset(acc1, acc2);
  ensures true == subset(acc_at_this_bucket(acc1, b),
                         acc_at_this_bucket(acc2, b));
  {
    switch(b) { case bucket(chains):
      subset_append2(acc1, acc2, chains);
      subset_append3(chains, acc2, chains);
      subset_append(acc1, chains, acc_at_this_bucket(acc2, b));
    }
  }

  lemma void holds_for_subset_wraparound<kt>(list<pair<kt, nat> > acc1,
                                             list<pair<kt, nat> > acc2,
                                             list<bucket<kt> > buckets,
                                             fixpoint (pair<kt,nat>,bool) prop)
  requires true == forall(get_wraparound(acc1, buckets), prop) &*&
           true == subset(acc2, acc1);
  ensures true == forall(get_wraparound(acc2, buckets), prop);
  {
    switch(buckets) {
      case nil:
        subset_forall(acc2, acc1, prop);
      case cons(bh,bt):
        acc_at_this_bucket_subset(acc2, acc1, bh);
        advance_acc_subset(acc_at_this_bucket(acc2, bh),
                           acc_at_this_bucket(acc1, bh));
        holds_for_subset_wraparound(advance_acc(acc_at_this_bucket(acc1, bh)),
                                    advance_acc(acc_at_this_bucket(acc2, bh)),
                                    bt, prop);
    }
  }

  lemma void buckets_ok_acc_bounded<kt>(list<bucket<kt> > buckets)
  requires true == buckets_ok(buckets);
  ensures true == forall(get_wraparound(nil, buckets), (upper_limit)(length(buckets)));
  {
    buckets_ok_acc_bounded_rec(get_wraparound(nil, buckets), buckets, length(buckets));
    holds_for_subset_wraparound(get_wraparound(nil, buckets), nil,
                                buckets, (upper_limit)(length(buckets)));
  }
  @*/
/*@
  fixpoint list<pair<kt, nat> > get_crossing_chains_rec_fp<kt>
       (list<pair<kt, nat> > acc,
        list<bucket<kt> > buckets,
        int index) {
    switch(buckets) {
      case nil: return acc; //index must be 0 here
      case cons(h,t):
        return (index == 0) ?
          (acc_at_this_bucket(acc, h)) :
          (get_crossing_chains_rec_fp
             (advance_acc(acc_at_this_bucket(acc, h)), t, index - 1));
    }
  }

  fixpoint list<pair<kt, nat> > get_crossing_chains_fp<kt>(list<bucket<kt> > buckets, int index) {
    return get_crossing_chains_rec_fp(get_wraparound(nil, buckets), buckets, index);
  }
  @*/

/*@
  lemma void wraparound_is_last_crossing_chains<kt>(list<pair<kt, nat> > acc, list<bucket<kt> > buckets)
  requires buckets != nil;
  ensures get_wraparound(acc, buckets) == get_crossing_chains_rec_fp(acc, buckets, length(buckets));
  {
    switch(buckets) {
      case nil: return;
      case cons(h,t):
        if (t == nil) {
        } else {
          wraparound_is_last_crossing_chains
            (advance_acc(acc_at_this_bucket(acc, h)), t);
          assert get_wraparound(acc, buckets) ==
                 get_wraparound(advance_acc(acc_at_this_bucket(acc, h)), t);
          switch(t) {
            case nil:
            case cons(th,tt):
          }
          assert get_crossing_chains_rec_fp(acc, buckets,
                                            length(buckets) - 1) ==
                 get_crossing_chains_rec_fp(advance_acc
                                              (acc_at_this_bucket(acc, h)),
                                            t, length(t) - 1);
        }
    }
  }
  @*/


/*@
  lemma void advance_acc_append_commute<kt>(list<pair<kt, nat> > acc1,
                                            list<pair<kt, nat> > acc2)
  requires true;
  ensures advance_acc(append(acc1, acc2)) ==
          append(advance_acc(acc1), advance_acc(acc2));
  {
    switch(acc1) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
        }
        advance_acc_append_commute(t, acc2);
    }
  }

  lemma void append_acc_at_this_commute<kt>(list<pair<kt, nat> > acc0,
                                            list<pair<kt, nat> > acc,
                                            bucket<kt> b)
  requires true;
  ensures acc_at_this_bucket(append(acc0, acc), b) ==
          append(acc0, acc_at_this_bucket(acc, b));
  {
    switch(b) { case bucket(chains):
      append_assoc(acc0, acc, chains);
    }
  }

  lemma void advance_acc_lower_limit<kt>(list<pair<kt, nat> > shrt,
                                         int uplim)
  requires true == forall(shrt, (upper_limit)(uplim));
  ensures true == forall(advance_acc(shrt), (upper_limit)(uplim - 1));
  {
    switch(shrt) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
        }
        advance_acc_lower_limit(t, uplim);
    }
  }

  lemma void upper_limit_nonpos_no_tail<kt>(list<pair<kt, nat> > shrt,
                                            int uplim)
  requires uplim <= 0 &*&
           true == forall(shrt, (upper_limit)(uplim));
  ensures shrt == nil;
  {
    switch(shrt) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
        }
    }
  }

  lemma void short_chains_dont_matter<kt>(list<pair<kt, nat> > shrt,
                                          list<pair<kt, nat> > acc,
                                          list<bucket<kt> > buckets,
                                          int uplim, int index)
  requires true == forall(shrt, (upper_limit)(uplim)) &*&
           uplim <= index &*&
           index <= length(buckets);
  ensures get_crossing_chains_rec_fp(append(shrt, acc), buckets, index) ==
          get_crossing_chains_rec_fp(acc, buckets, index);
  {
    switch(buckets) {
      case nil:
        upper_limit_nonpos_no_tail(shrt, uplim);
      case cons(h,t):
        if (index == 0) {
          upper_limit_nonpos_no_tail(shrt, uplim);
        } else {
          advance_acc_append_commute(shrt, acc_at_this_bucket(acc,h));
          append_acc_at_this_commute(shrt, acc, h);
          advance_acc_lower_limit(shrt, uplim);
          short_chains_dont_matter(advance_acc(shrt),
                                   advance_acc(acc_at_this_bucket(acc, h)),
                                   t, uplim - 1, index - 1);
        }
    }
  }
  @*/

/*@
  lemma void buckets_ok_get_wraparound_idemp<kt>(list<bucket<kt> > buckets)
  requires true == buckets_ok(buckets) &*& buckets != nil;
  ensures get_wraparound(nil, buckets) ==
          get_wraparound(get_wraparound(nil, buckets), buckets);
  {
    buckets_ok_acc_bounded(buckets);
    short_chains_dont_matter(get_wraparound(nil, buckets), nil,
                             buckets, length(buckets), length(buckets));
    wraparound_is_last_crossing_chains(nil, buckets);
    wraparound_is_last_crossing_chains(get_wraparound(nil, buckets), buckets);
  }
  @*/


/*@
  fixpoint bool bucket_has_key_fp<kt>(kt k, bucket<kt> b) {
    switch(b) { case bucket(chains):
      return mem(k, map(fst, chains));
    }
  }
  @*/

/*@
  lemma void no_crossing_chains_rec<kt>(list<pair<kt, nat> > acc,
                                        list<bucket<kt> > buckets,
                                        int index)
  requires 0 <= index &*& index < length(buckets) &*&
           nth(index, buckets_get_chns_rec_fp(acc, buckets)) == 0;
  ensures nil == get_crossing_chains_rec_fp(acc, buckets, index);
  {
    switch(buckets) {
      case nil: return;
      case cons(bh,bt):
        if (0 == index) {
          assert get_crossing_chains_rec_fp(acc, buckets, index) ==
                 acc_at_this_bucket(acc, bh);

          length_0_nil(acc_at_this_bucket(acc, bh));
        } else {
          no_crossing_chains_rec(advance_acc(acc_at_this_bucket(acc, bh)),
                                 bt, index - 1);
        }
    }
  }

  lemma void no_crossing_chains_here<kt>(list<bucket<kt> > buckets,
                                         int index)
  requires 0 <= index &*& index < length(buckets) &*&
           nth(index, buckets_get_chns_fp(buckets)) == 0;
  ensures nil == get_crossing_chains_fp(buckets, index);
  {
    no_crossing_chains_rec(get_wraparound(nil, buckets), buckets, index);
  }
  @*/

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
  fixpoint hmap<kt> buckets_get_hmap_fp<kt>(list<bucket<kt> > buckets,
                                            fixpoint (kt,int) hash) {
    return hmap(buckets_get_keys_fp(buckets),
                get_keys_hashes_fp(buckets_get_keys_fp(buckets), hash));
  }
  @*/

/*@

  predicate pred_mapping<t>(list<void*> pts, list<int> bbs,
                            predicate (void*; t) pred;
                            list<option<t> > ks) =
            bbs == nil ? (ks == nil &*& pts == nil) :
              (pred_mapping(tail(pts), tail(bbs), pred, ?kst) &*&
               pts != nil &*&
               (head(bbs) == 0 ? ks == cons(none, kst) :
                 ([0.5]pred(head(pts), ?ksh) &*& ks == cons(some(ksh), kst))));

  fixpoint bool no_dups<t>(list<option<t> > l) {
    switch(l) {
      case nil: return true;
      case cons(h,t):
        return no_dups(t) && (h == none || !(mem(h, t)));
    }
  }

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
            true == no_dups(ks) &*&
            true == hash_list(ks, khs, hash) &*&
            m == hmap(ks, khs);
@*/

/*@
  predicate buckets_hmap_insync<kt>(int* chns, int capacity,
                                    hmap<kt> m, list<bucket<kt> > buckets,
                                    fixpoint (kt, int) hash) =
    ints(chns, capacity, buckets_get_chns_fp(buckets)) &*&
    true == buckets_ok(buckets) &*&
    m == buckets_get_hmap_fp(buckets, hash) &*&
    true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash);

  @*/

/*@
  lemma void rem_preserves_no_mem<kt>(list<option<kt> > ks, kt k, int i)
  requires false == mem(some(k), ks);
  ensures false == mem(some(k), update(i, none, ks));
  {
    switch(ks) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          rem_preserves_no_mem(t, k, i-1);
        }
    }
  }

  lemma void hmap_rem_preserves_no_dups<kt>(list<option<kt> > ks, int i)
  requires true == no_dups(ks) &*& 0 <= i;
  ensures true == no_dups(update(i, none, ks));
  {
    switch(ks) {
     case nil: return;
     case cons(h,t):
       if (i == 0) {
       } else {
         hmap_rem_preserves_no_dups(t, i-1);
         if (h == none){
         } else {
           assert(false == mem(h, t));
           some_get_some(h);
           rem_preserves_no_mem(t, get_some(h), i-1);
         }
       }
       return;
    }
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
  lemma void overshoot_bucket<kt>(list<bucket<kt> > buckets, int shift, int capacity,
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
  lemma void this_bucket_still_no_key<kt>(list<pair<kt, nat> > acc, bucket<kt> bh, kt k)
  requires false == mem(k, map(fst, acc)) &*&
           false == bucket_has_key_fp(k, bh);
  ensures false == mem(k, map(fst, acc_at_this_bucket(acc, bh)));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void advance_acc_still_no_key<kt>(list<pair<kt, nat> > acc, kt k)
  requires false == mem(k, map(fst, acc));
  ensures false == mem(k, map(fst, advance_acc(acc)));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void no_key_certainly_not_here<kt>(list<pair<kt, nat> > acc, kt k)
  requires false == mem(k, map(fst, acc));
  ensures get_current_key_fp(acc) != some(k);
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void some_bucket_contains_key_rec<kt>(list<pair<kt, nat> > acc, list<bucket<kt> > buckets, kt k)
  requires true == mem(some(k), buckets_get_keys_rec_fp(acc, buckets)) &*&
           false == mem(k, map(fst, acc));
  ensures true == exists(buckets, (bucket_has_key_fp)(k));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (bucket_has_key_fp(k, h)) {
        } else {
          this_bucket_still_no_key(acc, h, k);
          advance_acc_still_no_key(acc_at_this_bucket(acc, h), k);
          assert false == mem(k, map(fst, advance_acc(acc_at_this_bucket(acc, h))));
          no_key_certainly_not_here(acc_at_this_bucket(acc, h), k);
          assert get_current_key_fp(acc_at_this_bucket(acc, h)) != some(k);
          some_bucket_contains_key_rec(advance_acc(acc_at_this_bucket(acc, h)), t, k);
        }
    }
  }
  @*/

/*@
  lemma void in_this_bucket_then_in_the_map<kt>(list<pair<kt, nat> > acc,
                                                list<bucket<kt> > buckets,
                                                int n, kt k, int bound)
  requires true == buckets_ok_rec(acc, buckets, bound) &*& 0 <= n &*& n < length(buckets) &*&
           true == bucket_has_key_fp(k, nth(n, buckets));
  ensures true == mem(some(k), buckets_get_keys_rec_fp(acc, buckets));
  {
    assume(false);//TODO
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
    assume(false);//TODO
  }
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
              in_this_bucket_then_in_the_map(acc, buckets,
                                             loop_fp(hash(k), capacity) - shift,
                                             k, capacity);
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

  lemma void key_is_contained_in_the_bucket<kt>(list<bucket<kt> > buckets, int capacity,
                                                fixpoint (kt,int) hash,
                                                kt k)
  requires true == key_chains_start_on_hash_fp(buckets, 0, capacity, hash) &*&
           0 < capacity &*&
           true == buckets_ok(buckets) &*&
           length(buckets) == capacity;
  ensures hmap_exists_key_fp(buckets_get_hmap_fp(buckets, hash), k) ==
          bucket_has_key_fp(k, nth(loop_fp(hash(k), capacity), buckets));
  {
    assert hmap_exists_key_fp(buckets_get_hmap_fp(buckets, hash), k) ==
           mem(some(k), buckets_get_keys_fp(buckets));
    loop_lims(hash(k), capacity);
    if (mem(k, map(fst, get_wraparound(nil, buckets)))) {
      assume(false);//TODO
    } else {
      key_is_contained_in_the_bucket_rec(buckets, get_wraparound(nil, buckets),
                                         0, capacity, hash, k);
    }
  }
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

  lemma void no_dups_same<kt>(list<option<kt> > ks, kt k, int n, int m)
  requires true == no_dups(ks) &*& 0 <= n &*& n < length(ks) &*&
           0 <= m &*& m < length(ks) &*&
           nth(n, ks) == some(k) &*& nth(m, ks) == some(k);
  ensures n == m;
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        if (n == 0) {
          assert(h == some(k));
          assert(!mem(h, t));
        } else if (m == 0) {
        } else {
          assert(0<n);
          assert(0<m);
          no_dups_same(t, k, n-1, m-1);
        }
    }
  }

  lemma void ks_find_this_key<kt>(list<option<kt> > ks, int i, kt k)
  requires nth(i, ks) == some(k) &*& true == no_dups(ks) &*&
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
  requires nth(i, hmap_ks_fp(m)) == some(k) &*& true == no_dups(hmap_ks_fp(m)) &*&
           0 <= i &*& i < length(hmap_ks_fp(m));
  ensures hmap_find_key_fp(m, k) == i;
  {
    ks_find_this_key(hmap_ks_fp(m), i, k);
  }

  fixpoint bool not_my_key<kt>(kt k, option<kt> arg) {
    return arg != some(k);
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

  lemma void up_to_nth_uncons<kt>(kt hd, list<kt> tl,
                                  nat n, fixpoint (kt, bool) prop)
  requires true == up_to(succ(n),
                         (nthProp)(cons(hd,tl), prop)) &*&
           int_of_nat(n) <= length(tl);
  ensures true == up_to(n, (nthProp)(tl, prop)) &*&
          true == prop(hd);
  {
    shift_for_all(cons(hd,tl), prop, 1, int_of_nat(succ(n)), n);
    shift_for_append(cons(hd,nil), tl, prop, n);
    up_to_covers_x(succ(n), (nthProp)(cons(hd,tl), prop), 0);
  }

  lemma void no_key_found<kt>(list<option<kt> > ks, kt k)
  requires true == up_to(nat_of_int(length(ks)), (nthProp)(ks, (not_my_key)(k)));
  ensures false == mem(some(k), ks);
  {
    switch(ks){
      case nil: return;
      case cons(h,t):
        up_to_nth_uncons(h, t, nat_of_int(length(t)), (not_my_key)(k));
        no_key_found(t, k);
    }
  }
@*/

/*@
  lemma void buckets_keys_chns_same_len_rec<kt>(list<pair<kt, nat> > acc,
                                             list<bucket<kt> > buckets)
  requires true;
  ensures length(buckets_get_keys_rec_fp(acc, buckets)) == length(buckets) &*&
          length(buckets_get_chns_rec_fp(acc, buckets)) == length(buckets);
  {
    switch(buckets) {
      case nil: return;
      case cons(h,t):
        buckets_keys_chns_same_len_rec(advance_acc(acc_at_this_bucket(acc, h)),
                                       t);
    }
  }

  lemma void buckets_keys_chns_same_len<kt>(list<bucket<kt> > buckets)
  requires true;
  ensures length(buckets_get_keys_fp(buckets)) == length(buckets) &*&
          length(buckets_get_chns_fp(buckets)) == length(buckets);
  {
    buckets_keys_chns_same_len_rec(get_wraparound(nil, buckets), buckets);
  }
  @*/

/*@
  lemma void nozero_no_current_key<kt>(list<pair<kt, nat> > acc)
  requires false == mem(zero, get_just_tails(acc));
  ensures get_current_key_fp(acc) == none;
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(k,dist):
          switch(dist) {
            case zero:
            case succ(n):
              nozero_no_current_key(t);
          }
        }
    }
  }

  lemma void advance_acc_preserves_key<kt>(list<pair<kt, nat> > acc, kt key)
  requires true == distinct(get_just_tails(acc)) &*& get_current_key_fp(acc) != some(key);
  ensures mem(key, map(fst, acc)) == mem(key, map(fst, advance_acc(acc)));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(k,dst):
          switch(dst) {
            case zero:
              nozero_no_current_key(t);
              assert get_current_key_fp(t) == none;
              if (k == key) {
              } else {
                advance_acc_preserves_key(t, key);
              }
            case succ(n):
              assert get_current_key_fp(t) == get_current_key_fp(acc);
              if (k == key) {
              } else {
                advance_acc_preserves_key(t, key);
              }
          }
        }
    }
  }

  lemma void next_cell_keeps_keys<kt>(list<pair<kt, nat> > acc, bucket<kt> b, kt k)
  requires true == mem(k, map(fst, acc)) &*&
           get_current_key_fp(acc_at_this_bucket(acc, b)) != some(k) &*&
           true == distinct(get_just_tails(acc_at_this_bucket(acc, b)));
  ensures true == mem(k, map(fst, advance_acc(acc_at_this_bucket(acc, b))));
  {
    switch(b) { case bucket(chains):
      map_append(fst, acc, chains);
      advance_acc_preserves_key(acc_at_this_bucket(acc, b), k);
    }
  }
  @*/

/*@
  lemma void next_i_cells_keep_keys<kt>(list<bucket<kt> > buckets,
                                        nat i,
                                        kt k,
                                        list<pair<kt, nat> > acc,
                                        int capacity)
  requires true == up_to(i,
                         (nthProp)(buckets_get_keys_rec_fp(acc, buckets),
                                   (not_my_key)(k))) &*&
           true == mem(k, map(fst, acc)) &*&
           true == buckets_ok_rec(acc, buckets, capacity) &*&
           int_of_nat(i) <= length(buckets);
  ensures true == mem(k, map(fst, get_crossing_chains_rec_fp(acc, buckets,
                                                             int_of_nat(i))));
  {
    switch(buckets) {
      case nil:
      case cons(bh,bt):
        switch(i) {
          case zero:
            switch(bh) { case bucket(chains):
              map_append(fst, acc, chains);
            }
          case succ(n):
            buckets_keys_chns_same_len_rec(acc, buckets);
            assert buckets_get_keys_rec_fp(acc, buckets) == cons(?bgkh, ?bgkt);
            up_to_nth_uncons(bgkh, bgkt, n, (not_my_key)(k));
            next_cell_keeps_keys(acc, bh, k);
            next_i_cells_keep_keys(bt, n, k,
                                   advance_acc(acc_at_this_bucket(acc, bh)),
                                   capacity);
        }
    }
  }
  @*/

/*@
  lemma void byLoopNthPropEqNthPropUpTo<t>(nat n, list<t> lst, fixpoint (t,bool) prop, int capacity)
  requires int_of_nat(n) <= capacity;
  ensures up_to(n, (byLoopNthProp)(lst, prop, capacity, 0)) == up_to(n, (nthProp)(lst, prop));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void upToByLoopNthPropShift1<t>(nat n, t hd, list<t> tl,
                                        fixpoint (t,bool) prop,
                                        int capacity, int start)
  requires true == up_to(n, (byLoopNthProp)(cons(hd,tl), prop, capacity, start)) &*&
           int_of_nat(n) + start <= capacity;
  ensures true == up_to(n, (byLoopNthProp)(tl, prop, capacity, start - 1));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void upToByLoopNthPropShiftN<t>(nat i, int shift, list<t> l,
                                        fixpoint (t,bool) prop,
                                        int capacity, int start)
  requires int_of_nat(i) + shift < capacity &*&
           0 <= shift &*& shift <= start &*&
           true == up_to(i, (byLoopNthProp)(l, prop, capacity, start));
  ensures true == up_to(i, (byLoopNthProp)(drop(shift, l), prop, capacity, start - shift));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void upToNthPropShift1<t>(nat n, t hd, list<t> tl, fixpoint (t,bool) prop)
  requires true;
  ensures up_to(succ(n), (nthProp)(cons(hd, tl), prop)) ==
          prop(hd) && up_to(n, (nthProp)(tl, prop));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void bucket_has_then_acc_has_key<kt>(bucket<kt> b, list<pair<kt, nat> > acc, kt k)
  requires true == bucket_has_key_fp(k, b);
  ensures true == mem(k, map(fst, acc_at_this_bucket(acc, b)));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void crossing_chains_keep_key_hlp_inbound<kt>(list<bucket<kt> > buckets,
                                                      nat i,
                                                      int start,
                                                      int capacity,
                                                      kt k,
                                                      list<pair<kt, nat> > acc)
  requires buckets != nil &*&
           true == up_to(i,
                         (byLoopNthProp)(buckets_get_keys_rec_fp(acc, buckets),
                                         (not_my_key)(k),
                                         capacity,
                                         start)) &*&
           start + int_of_nat(i) <= length(buckets) &*&
           length(buckets) <= capacity &*&
           0 <= start &*&
           true == buckets_ok_rec(acc, buckets, capacity) &*&
           start < length(buckets) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures true == mem(k, map(fst, get_crossing_chains_rec_fp(acc, buckets, start + int_of_nat(i))));
  {
    switch(buckets) {
      case nil: return;
      case cons(h,t):
        if (start == 0) {
          bucket_has_then_acc_has_key(h, acc, k);
          byLoopNthPropEqNthPropUpTo(i, buckets_get_keys_rec_fp(acc, buckets),
                                     (not_my_key)(k), capacity);
          assert true == up_to(i, (nthProp)(buckets_get_keys_rec_fp(acc, buckets),
                                            (not_my_key)(k)));
          switch(i) {
            case zero:
            case succ(n):
              assert buckets_get_keys_rec_fp(acc, buckets) ==
                     cons(get_current_key_fp(acc_at_this_bucket(acc, h)),
                          buckets_get_keys_rec_fp(advance_acc(acc_at_this_bucket(acc, h)), t));
              upToNthPropShift1(n, get_current_key_fp(acc_at_this_bucket(acc, h)),
                                buckets_get_keys_rec_fp(advance_acc(acc_at_this_bucket(acc, h)), t), (not_my_key)(k));
              assert true == up_to(n, (nthProp)(buckets_get_keys_rec_fp(advance_acc(acc_at_this_bucket(acc, h)), t), (not_my_key)(k)));
              assert true == not_my_key(k, get_current_key_fp(acc_at_this_bucket(acc, h)));
              assert true == mem(k, map(fst, acc_at_this_bucket(acc, h)));
              advance_acc_preserves_key(acc_at_this_bucket(acc, h), k);
              assert true == mem(k, map(fst, advance_acc(acc_at_this_bucket(acc, h))));
              assert int_of_nat(i) <= length(buckets);
              assert int_of_nat(n) <= length(t);
              next_i_cells_keep_keys(t, n, k, advance_acc(acc_at_this_bucket(acc, h)), capacity);
          }

        } else {
          upToByLoopNthPropShift1(i, get_current_key_fp(acc_at_this_bucket(acc, h)),
                                  buckets_get_keys_rec_fp(advance_acc(acc_at_this_bucket(acc, h)), t),
                                  (not_my_key)(k),
                                  capacity,
                                  start);
          crossing_chains_keep_key_hlp_inbound(t, i, start - 1, capacity, k, advance_acc(acc_at_this_bucket(acc, h)));
        }
    }
  }
  @*/

/*@
  lemma void crossing_chains_keep_key_inbound<kt>(list<bucket<kt> > buckets,
                                                  nat i,
                                                  int start,
                                                  int capacity,
                                                  kt k)
  requires buckets != nil &*&
           true == up_to(i,
                         (byLoopNthProp)(buckets_get_keys_fp(buckets),
                                         (not_my_key)(k),
                                         capacity,
                                         start)) &*&
           true == bucket_has_key_fp(k, nth(start, buckets)) &*&
           0 <= start &*&
           start < length(buckets) &*&
           length(buckets) == capacity &*&
           true == buckets_ok(buckets) &*&
           start + int_of_nat(i) <= capacity;
  ensures true == mem(k, map(fst, get_crossing_chains_fp(buckets, start + int_of_nat(i))));
  {
    crossing_chains_keep_key_hlp_inbound(buckets, i, start, capacity, k, get_wraparound(nil, buckets));
  }
  @*/

/*@
  lemma void break_down_up_to_by_loop<t>(list<t> lst, int i, int start, int capacity,
                                         fixpoint (t,bool) prop)
  requires capacity <= length(lst) &*&
           0 <= start &*& start < capacity &*&
           capacity <= start + i &*&
           true == up_to(nat_of_int(i),
                         (byLoopNthProp)(lst, prop, capacity, start));
  ensures true == up_to(nat_of_int(capacity - start),
                        (byLoopNthProp)(lst, prop, capacity, start)) &*&
          true == up_to(nat_of_int(start + i - capacity),
                        (nthProp)(lst, prop));
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void crossing_chains_keep_key<kt>(list<bucket<kt> > buckets,
                                          int i,
                                          int start,
                                          int capacity,
                                          kt k)
  requires 0 <= i &*&
           0 <= start &*&
           start < length(buckets) &*&
           start + i - capacity + 1 <= capacity &*&
           buckets != nil &*&
           true == buckets_ok(buckets) &*&
           length(buckets) == capacity &*&
           true == up_to(nat_of_int(i),
                         (byLoopNthProp)(buckets_get_keys_fp(buckets),
                                         (not_my_key)(k),
                                         capacity,
                                         start)) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures true == mem(k, map(fst, get_crossing_chains_fp(buckets, loop_fp(start + i, capacity))));
  {
    if (capacity <= start + i) {
      buckets_keys_chns_same_len(buckets);
      break_down_up_to_by_loop(buckets_get_keys_fp(buckets), i, start, capacity, (not_my_key)(k));
      //assume( true == mem(k, map(fst, get_wraparound(nil, buckets))));
      crossing_chains_keep_key_inbound(buckets, nat_of_int(capacity - start), start, capacity, k);
      wraparound_is_last_crossing_chains(get_wraparound(nil, buckets), buckets);
      assert get_wraparound(get_wraparound(nil, buckets), buckets) == get_crossing_chains_fp(buckets, length(buckets));
      assert true == mem(k, map(fst, get_crossing_chains_fp(buckets,
                                                            start + int_of_nat(nat_of_int(capacity - start)))));
      assert true == mem(k, map(fst, get_crossing_chains_fp(buckets, capacity)));
      buckets_ok_get_wraparound_idemp(buckets);

      assert get_wraparound(nil, buckets) == get_wraparound(get_wraparound(nil, buckets), buckets);
      assert get_wraparound(nil, buckets) == get_crossing_chains_fp(buckets, capacity);

      //assume(get_current_key_fp(get_crossing_chains_fp(buckets, capacity - 1)) != some(k)); //TODO
      //assert get_current_key_fp(get_crossing_chains_fp(buckets, capacity - 1)) != some(k);
      //assume(mem(k, map(fst, get_crossing_chains_fp(buckets, capacity)))); //TODO
      assert true == mem(k, map(fst, get_crossing_chains_fp(buckets, capacity)));
      assert true == mem(k, map(fst, get_wraparound(get_wraparound(nil, buckets), buckets)));

      assert true == mem(k, map(fst, get_wraparound(nil, buckets)));
      next_i_cells_keep_keys(buckets, nat_of_int(start + i - capacity), k, get_wraparound(nil, buckets), capacity);
      loop_injection(start + i - capacity, capacity);
      loop_bijection(start + i - capacity, capacity);
      assert loop_fp(start + i, capacity) == (start + i - capacity);
    } else {
      crossing_chains_keep_key_inbound(buckets, nat_of_int(i), start, capacity, k);
      loop_bijection(start + i, capacity);
    }
  }
  @*/

/*@
  lemma void chains_depleted_no_hope<kt>(list<bucket<kt> > buckets,
                                         int i,
                                         int start,
                                         kt k,
                                         int capacity,
                                         fixpoint (kt,int) hash)
  requires buckets != nil &*&
           true == up_to(nat_of_int(i),
                         (byLoopNthProp)(buckets_get_keys_fp(buckets),
                                         (not_my_key)(k),
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
int find_key/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* chns,
                         void* keyp, map_keys_equality* eq, int key_hash,
                         int capacity)
/*@ requires hmapping<kt>(?kpr, ?hsh, capacity, busybits, ?kps, k_hashes, ?hm) &*&
             buckets_hmap_insync(chns, capacity, hm, ?buckets, hsh) &*&
             pointers(keyps, capacity, kps) &*&
             [?kfr]kpr(keyp, ?k) &*&
             hsh(k) == key_hash &*&
             [?f]is_map_keys_equality<kt>(eq, kpr); @*/
/*@ ensures hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm) &*&
            buckets_hmap_insync(chns, capacity, hm, buckets, hsh) &*&
            pointers(keyps, capacity, kps) &*&
            [kfr]kpr(keyp, k) &*&
            [f]is_map_keys_equality<kt>(eq, kpr) &*&
            (hmap_exists_key_fp(hm, k) ?
             (result == hmap_find_key_fp(hm, k)) :
             (result == -1)); @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ open buckets_hmap_insync(chns, capacity, hm, buckets, hsh);
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
                                (byLoopNthProp)(ks, (not_my_key)(k),
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
        //@ close buckets_hmap_insync(chns, capacity, hm, buckets, hsh);
        return index;
      }
      //@ recover_pred_mapping(kps, bbs, ks, index);
    } else {
      if (chn == 0) {
        //@ assert length(chnlist) == capacity;
        //@ buckets_keys_chns_same_len(buckets);
        //@ assert length(buckets) == capacity;
        //@ no_crossing_chains_here(buckets, index);
        //@ assert nil == get_crossing_chains_fp(buckets, index);
        //@ key_is_contained_in_the_bucket(buckets, capacity, hsh, k);
        //@ assert true == up_to(nat_of_int(i), (byLoopNthProp)(ks, (not_my_key)(k), capacity, start));
        //@ assert true == up_to(nat_of_int(i), (byLoopNthProp)(ks, (not_my_key)(k), capacity, loop_fp(hsh(k), capacity)));
        //@ assert buckets != nil;
        //@ chains_depleted_no_hope(buckets, i, loop_fp(hsh(k), capacity), k, capacity, hsh);
        //@ assert false == hmap_exists_key_fp(hm, k);
        //@ close hmapping<kt>(kpr, hsh, capacity, busybits, kps, k_hashes, hm);
        //@ close buckets_hmap_insync(chns, capacity, hm, buckets, hsh);
        return -1;
      }
      //@ assert(length(ks) == capacity);
      //@ if (bb != 0) no_hash_no_key(ks, khs, k, index, hsh);
      //@ if (bb == 0) no_bb_no_key(ks, bbs, index);
    }
    //@ assert(nth(index, ks) != some(k));
    //@ assert(true == not_my_key(k, nth(index, ks)));
    //@ assert(true == not_my_key(k, nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, (not_my_key)(k), start, capacity, nat_of_int(capacity));
  //@ no_key_found(ks, k);
  //@ close buckets_hmap_insync(chns, capacity, hm, buckets, hsh);
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
          keyp(nth(index, kps), k);
  {
    assume(false);//TODO
  }
  @*/

static
int find_key_remove_chain/*@ <kt> @*/(int* busybits, void** keyps,
                                      int* k_hashes, int* chns,
                                      int start,
                                      void* keyp, map_keys_equality* eq,
                                      int key_hash,
                                      int capacity,
                                      void** keyp_out)
/*@ requires hmapping<kt>(?kpr, ?hsh, capacity, busybits, ?kps, k_hashes, ?hm) &*&
             buckets_hmap_insync(chns, capacity, hm, ?buckets, hsh) &*&
             pointers(keyps, capacity, kps) &*&
             [?kfr]kpr(keyp, ?k) &*&
             hsh(k) == key_hash &*&
             0 <= start &*& start < capacity &*&
             [?f]is_map_keys_equality<kt>(eq, kpr) &*&
             true == hmap_exists_key_fp(hm, k)
             &*& *keyp_out |-> _; @*/
/*@ ensures hmapping<kt>(kpr, hsh, capacity,
                         busybits, kps, k_hashes,
                         hmap_rem_key_fp(hm, hmap_find_key_fp(hm, k))) &*&
            buckets_hmap_insync(chns, capacity,
                                hmap_rem_key_fp(hm, hmap_find_key_fp(hm, k)),
                                buckets_remove_key_fp(buckets, k), hsh) &*&
            pointers(keyps, capacity, kps) &*&
            [kfr]kpr(keyp, k) &*&
            [f]is_map_keys_equality<kt>(eq, kpr) &*&
            result == hmap_find_key_fp(hm, k); @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ open buckets_hmap_insync(chns, capacity, hm, buckets, hsh);
  //@ assert ints(chns, capacity, ?chnlist);
  //@ assert pred_mapping(kps, ?bbs, kpr, ?ks);
  //@ assert hm == hmap(ks, ?khs);
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
                  *keyp_out |-> _ &*&
                  true == up_to(nat_of_int(i),
                                (byLoopNthProp)(ks, (not_my_key)(k),
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
        return index;
      }
      //@ recover_pred_mapping(kps, bbs, ks, index);
    } else {
      //@ assert 0 < chn;
      chns[index] = chn - 1;
      //@ assert(length(ks) == capacity);
      //@ if (bb != 0) no_hash_no_key(ks, khs, k, index, hsh);
      //@ if (bb == 0) no_bb_no_key(ks, bbs, index);
    }
    //@ assert(nth(index, ks) != some(k));
    //@ assert(true == not_my_key(k, nth(index, ks)));
    //@ assert(true == not_my_key(k, nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, (not_my_key)(k), start, capacity, nat_of_int(capacity));
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
        up_to_nth_uncons(h, t, cell_busy);
        full_size(t);
    }
  }
  @*/

static
int find_empty/*@ <kt> @*/(int* busybits, int* chns, int start, int capacity)
/*@ requires hmapping<kt>(?kp, ?hsh, capacity, busybits, ?kps, ?k_hashes, ?hm) &*&
             pointers(?keyps, capacity, kps) &*&
             0 <= start &*& start < capacity; @*/
/*@ ensures hmapping<kt>(kp, hsh, capacity, busybits, kps, k_hashes, hm) &*&
            pointers(keyps, capacity, kps) &*&
            (hmap_size_fp(hm) < capacity ?
             (true == hmap_empty_cell_fp(hm, result) &*&
              0 <= result &*& result < capacity) :
             result == -1) ; @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ assert pred_mapping(kps, ?bbs, kp, ?ks);
  //@ assert hm == hmap(ks, ?khs);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant pred_mapping(kps, bbs, kp, ks) &*&
                  ints(busybits, capacity, bbs) &*&
                  ints(k_hashes, capacity, khs) &*&
                  pointers(keyps, capacity, kps) &*&
                  0 <= i &*& i <= capacity &*&
                  true == up_to(nat_of_int(i),
                                (byLoopNthProp)(ks, cell_busy,
                                                capacity, start));
      @*/
    //@ decreases capacity - i;
  {
    //@ pred_mapping_same_len(bbs, ks);
    int index = loop(start + i, capacity);
    int bb = busybits[index];
    if (0 == bb) {
      //@ zero_bbs_is_for_empty(bbs, ks, index);
      //@ close hmapping<kt>(kp, hsh, capacity, busybits, kps, k_hashes, hm);
      return index;
    }
    chns[index]++;
    //@ bb_nonzero_cell_busy(bbs, ks, index);
    //@ assert(true == cell_busy(nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, cell_busy, start, capacity, nat_of_int(capacity));
  //@ full_size(ks);
  //@ close hmapping<kt>(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  return -1;
}

/*@
  fixpoint list<int> zero_list_fp(nat len) {
    switch(len) {
      case zero: return nil;
      case succ(x): return cons(0, zero_list_fp(x));
    }
  }

  fixpoint list<option<kt> > none_list_fp<kt>(nat len) {
    switch(len) {
      case zero: return nil;
      case succ(l): return cons(none,none_list_fp(l));
    }
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
  ensures true == no_dups(none_list_fp(len));
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
     buckets_hmap_insync<kt>(chns, capacity, hm, ?buckets, hash) &*&
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

void map_initialize/*@ <kt> @*/(int* busybits, map_keys_equality* eq,
                                void** keyps, int* khs, int* chns,
                                int* vals, int capacity)
/*@ requires map_key_type<kt>(_) &*& map_key_hash<kt>(?hash) &*&
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
  //@ open map_key_type(_);
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
                  0 < capacity &*& 2*capacity < INT_MAX &*&
                  0 <= i &*& i <= capacity;
      @*/
    //@ decreases capacity - i;
  {
    //@ move_int(busybits, i, capacity);
    //@ extend_zero_list(nat_of_int(i), head(drop(i,bbs)));
    busybits[i] = 0;
    chns[i] = 0;
    //@ assert(succ(nat_of_int(i)) == nat_of_int(i+1));
    //@ tail_drop(bbs, i);
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
  requires key_vals(ks, ?val_arr, m) &*& true == no_dups(ks);
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
  requires key_vals(ks, val_arr, m) &*& true == no_dups(ks) &*&
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
           true == no_dups(hmap_ks_fp(hm)) &*&
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

int map_get/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* chns,
                        int* values,
                        void* keyp, map_keys_equality* eq, int hash, int* value,
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
  requires false == mem(some(k), ks) &*& true == no_dups(ks);
  ensures true == no_dups(update(i, some(k), ks));
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
           nth(i, ks) == none &*& 0 <= i &*&
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

void map_put/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* chns,
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
  int index = find_empty(busybits, chns, start, capacity);

  //@ hmap_map_size(hm, m);

  //@ open hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  //@ assert pred_mapping(kps, ?bbs, kp, ?ks);
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
  /*@ close mapping(map_put_fp(m, k, value), map_put_fp(addrs, k, keyp),
                    kp, recp, hsh, capacity, busybits, keyps, k_hashes, chns, values);
    @*/
}

/*@
  lemma void hmap_rem_preserves_pred_mapping<kt>(list<char*> kps, list<int> bbs,
                                                 predicate (void*;kt) keyp,
                                                 list<option<kt> > ks,
                                                 int i)
  requires pred_mapping(kps, bbs, keyp, ks) &*& 0 <= i &*& nth(i, ks) == some(?k);
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
           true == no_dup_keys(m) &*& true == no_dups(ks) &*&
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
           true == no_dups(hmap_ks_fp(hm)) &*&
           0 <= i &*& i < length(hmap_ks_fp(hm));
  ensures key_vals(hmap_ks_fp(hmap_rem_key_fp(hm, i)),
                   vals, map_erase_fp(m, k));
  {
     map_no_dups(hmap_ks_fp(hm), m);
     hmap_ks_hmap_rm(hm, i);
     ks_rem_map_erase_coherent(hmap_ks_fp(hm), m, i, k);
  }
  @*/

void map_erase/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* chns,
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
  int start = loop(hash, capacity);
  //@ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  find_key_remove_chain(busybits, keyps, k_hashes, chns, start,
                        keyp, eq, hash, capacity, keyp_out);
  //@ hmap_exists_iff_map_has(hm, m, k);
  //@ hmapping_ks_capacity(hm, capacity);
  //@ assert(index < capacity);
  //@ open hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hm);
  //@ assert(pred_mapping(kps, ?bbs, kp, ?ks));
  //@ assert(ints(k_hashes, capacity, ?khs));
  //@ hmap_find_returns_the_key(hm, kps, addrs, k);
  //@ mem_nth_index_of(some(k), ks);
  //@ hmap_rem_preserves_pred_mapping(kps, bbs, kp, ks, index);
  //@ hmap_rem_preserves_no_dups(ks, index);
  //@ hmap_rem_preserves_hash_list(ks, khs, hsh, index);
  //@ close hmapping(kp, hsh, capacity, busybits, kps, k_hashes, hmap_rem_key_fp(hm, index));
  //@ map_erase_preserves_rec_props(m, recp, k);
  //@ hmap_rem_map_erase_coherent(hm, m, index, k);
  //@ hmap_rem_map_erase_coherent(hm, addrs, index, k);
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

int map_size/*@ <kt> @*/(int* busybits, int capacity)
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
                  true == no_dups(ks) &*&
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
