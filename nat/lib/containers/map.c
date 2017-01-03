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
               forall(acc, (upper_limit)(bound - 1));
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

  fixpoint bucket<kt> bucket_put_key_fp<kt>(bucket<kt> b,
                                            kt k, int dist) {
    switch(b) { case bucket(chains):
      return bucket(cons(pair(k, nat_of_int(dist)), chains));
    }
  }

  fixpoint list<bucket<kt> >
  buckets_put_key_fp<kt>(list<bucket<kt> > buckets, kt k,
                         int start, int dist) {
    switch(buckets) {
      case nil: return nil;
      case cons(h,t):
        return (start == 0) ?
          cons(bucket_put_key_fp(h, k, dist), t) :
          cons(h, buckets_put_key_fp(t, k, start - 1, dist));
    }
  }

  fixpoint bool buckets_ok<kt>(list<bucket<kt> > buckets) {
    return buckets_ok_rec(get_wraparound(nil, buckets), buckets, length(buckets));
  }

  fixpoint bool nonneg(int x) { return 0 <= x; }

  fixpoint list<int> buckets_get_chns_rec_fp<kt>(list<pair<kt, nat> > acc,
                                                 list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil: return nil;
      case cons(bh,bt):
        return cons(length(advance_acc(acc_at_this_bucket(acc, bh))),
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
  @*/

/*@
  lemma void buckets_ok_wraparound_bounded_rec<kt>(list<pair<kt, nat> > acc,
                                                   list<bucket<kt> > buckets,
                                                   int bound)
  requires true == buckets_ok_rec(acc, buckets, bound);
  ensures true == forall(get_wraparound(acc, buckets), (upper_limit)(bound - 1));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_ok_wraparound_bounded_rec
          (advance_acc(acc_at_this_bucket(acc, h)),
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
      append_both_subset(acc1, chains, acc2);
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

  lemma void buckets_ok_wraparound_bounded<kt>(list<bucket<kt> > buckets)
  requires true == buckets_ok(buckets);
  ensures true == forall(get_wraparound(nil, buckets),
                         (upper_limit)(length(buckets) - 1));
  {
    buckets_ok_wraparound_bounded_rec
      (get_wraparound(nil, buckets), buckets, length(buckets));
    holds_for_subset_wraparound(get_wraparound(nil, buckets), nil,
                                buckets, (upper_limit)(length(buckets)-1));
  }
  @*/
/*@
  fixpoint list<pair<kt, nat> > get_crossing_chains_rec_fp<kt>
       (list<pair<kt, nat> > acc,
        list<bucket<kt> > buckets,
        int index) {
    switch(buckets) {
      case nil: return acc; //index must be -1 here
      case cons(h,t):
        return (index == 0) ?
          (advance_acc(acc_at_this_bucket(acc, h))) :
          (get_crossing_chains_rec_fp
             (advance_acc(acc_at_this_bucket(acc, h)), t, index - 1));
    }
  }

  fixpoint list<pair<kt, nat> > get_crossing_chains_fp<kt>(list<bucket<kt> > buckets, int index) {
    return get_crossing_chains_rec_fp(get_wraparound(nil, buckets), buckets, index);
  }
  @*/

/*@
  lemma void wraparound_is_last_crossing_chains<kt>(list<pair<kt, nat> > acc,
                                                    list<bucket<kt> > buckets)
  requires true;
  ensures get_wraparound(acc, buckets) ==
          get_crossing_chains_rec_fp(acc, buckets, length(buckets) - 1);
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
           uplim <= index + 1 &*&
           index + 1 <= length(buckets);
  ensures get_crossing_chains_rec_fp(append(shrt, acc), buckets, index) ==
          get_crossing_chains_rec_fp(acc, buckets, index);
  {
    switch(buckets) {
      case nil:
        upper_limit_nonpos_no_tail(shrt, uplim);
      case cons(h,t):
        advance_acc_append_commute(shrt, acc_at_this_bucket(acc,h));
        append_acc_at_this_commute(shrt, acc, h);
        advance_acc_lower_limit(shrt, uplim);
        if (index == 0) {
          upper_limit_nonpos_no_tail(advance_acc(shrt), uplim - 1);
        } else {
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
    buckets_ok_wraparound_bounded(buckets);
    short_chains_dont_matter(get_wraparound(nil, buckets), nil,
                             buckets, length(buckets) - 1, length(buckets) - 1);
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
                 advance_acc(acc_at_this_bucket(acc, bh));

          length_0_nil(advance_acc(acc_at_this_bucket(acc, bh)));
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
  lemma void this_bucket_still_no_key<kt>(list<pair<kt, nat> > acc, bucket<kt> bh, kt k)
  requires false == mem(k, map(fst, acc)) &*&
           false == bucket_has_key_fp(k, bh);
  ensures false == mem(k, map(fst, acc_at_this_bucket(acc, bh)));
  {
    switch(bh) { case bucket(chains):
      map_append(fst, acc, chains);
    }
  } //took 5m
  @*/


/*@
  lemma void advance_acc_still_no_key<kt>(list<pair<kt, nat> > acc, kt k)
  requires false == mem(k, map(fst, acc));
  ensures false == mem(k, map(fst, advance_acc(acc)));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
        }
        advance_acc_still_no_key(t, k);
    }
  }//took 4m
  @*/

/*@
  lemma void no_key_certainly_not_here<kt>(list<pair<kt, nat> > acc, kt k)
  requires false == mem(k, map(fst, acc));
  ensures get_current_key_fp(acc) != some(k);
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
              no_key_certainly_not_here(t, k);
          }
        }
    }
  }//took 5m
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
  lemma void in_this_bucket_then_in_the_map<kt>(list<bucket<kt> > buckets,
                                                int n, kt k, int bound,
                                                list<pair<kt, nat> > acc)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           0 <= n &*& n < length(buckets) &*&
           true == bucket_has_key_fp(k, nth(n, buckets));
  ensures true == mem(some(k), buckets_get_keys_rec_fp(acc, buckets));
  {
    assume(false);//TODO 30m
  }//debugged VeriFast:Redux for 30m, not done yet
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
  key_in_wraparound_then_key_in_a_bucket<kt>(list<bucket<kt> > buckets, kt k,
                                             list<pair<kt, nat> > acc)
  requires true == mem(k, map(fst, get_wraparound(acc, buckets))) &*&
           false == mem(k, map(fst, acc));
  ensures true == exists(buckets, (bucket_has_key_fp)(k));
  {
    switch(buckets) {
      case nil:
      case cons(bh,bt):
        if (bucket_has_key_fp(k, bh)) {
        } else {
          this_bucket_still_no_key(acc, bh, k);
          advance_acc_still_no_key(acc_at_this_bucket(acc, bh), k);
          key_in_wraparound_then_key_in_a_bucket
            (bt, k, advance_acc(acc_at_this_bucket(acc, bh)));
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
  lemma int key_index_in_acc<kt>(kt k, list<pair<kt, nat> > acc)
  requires true == mem(k, map(fst, acc));
  ensures 0 <= result &*& result < length(acc) &*&
          nth(result, acc) == pair(k, ?dist);
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        if (fst(h) == k) return 0;
        int tail_index = key_index_in_acc(k, t);
        return 1 + tail_index;
    }
  }
  @*/

/*@
  lemma void mem_advance_acc_swap<kt>(list<pair<kt, nat> > acc,
                                      kt k, nat d)
  requires true;
  ensures mem(pair(k, d), advance_acc(acc)) == mem(pair(k, succ(d)), acc);
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(hk,hd):
          switch(hd) {
            case zero:
              mem_advance_acc_swap(t, k, d);
            case succ(hdn):
              if (h != pair(k, succ(d))) {
                mem_advance_acc_swap(t, k, d);
              }
          }
        }
    }
  
  }
  @*/


/*@
  lemma void advance_acc_reduces_chain<kt>(list<pair<kt, nat> > acc,
                                           pair<kt, nat> chain)
  requires true == mem(chain, acc) &*& chain == pair(?k,succ(?n));
  ensures true == mem(pair(k,n), advance_acc(acc));
  {
    mem_advance_acc_swap(acc, k, n);
  }
  @*/

/*@
  lemma void
  distinct_and_zero_this_is_the_key<kt>(list<pair<kt, nat> > acc, kt k)
  requires true == mem(pair(k,zero), acc) &*&
           true == distinct(get_just_tails(acc));
  ensures get_current_key_fp(acc) == some(k);
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,distance):
          switch(distance) {
            case zero:
              if (h != pair(k, zero)) {
                assert true == mem(pair(k,zero), t);
                mem_map(pair(k,zero), t, snd);
                assert true == mem(zero, map(snd, t));
                assert false;
              }
            case succ(n):
              distinct_and_zero_this_is_the_key(t, k);
          }
        }
    }
  }
  @*/

/*@
  lemma void key_in_acc_then_in_hmap<kt>(list<pair<kt, nat> > acc,
                                         list<bucket<kt> > buckets,
                                         pair<kt, nat> chain,
                                         int bound)
  requires chain == pair(?k,?dist) &*&
           true == mem(chain, acc) &*&
           int_of_nat(dist) < length(buckets) &*&
           true == buckets_ok_rec(acc, buckets, bound);
  ensures true == mem(some(k), buckets_get_keys_rec_fp(acc, buckets));
  {
    switch(buckets) {
      case nil:
      case cons(bh,bt):
        switch(bh) { case bucket(chains):
          switch(dist) {
            case zero:
              distinct_and_zero_this_is_the_key(acc_at_this_bucket(acc, bh), k);
            case succ(n):
              advance_acc_reduces_chain(acc_at_this_bucket(acc, bh), chain);
              key_in_acc_then_in_hmap(advance_acc(acc_at_this_bucket(acc, bh)),
                                      bt, pair(k,n), bound);
          }
        }
    }
  }
  @*/

/*@
  lemma void key_in_wraparound_then_in_hmap<kt>(list<bucket<kt> > buckets,
                                                kt k)
  requires true == mem(k, map(fst, get_wraparound(nil, buckets))) &*&
           true == buckets_ok(buckets);
  ensures true == mem(some(k), buckets_get_keys_fp(buckets));
  {
    int pindex = key_index_in_acc(k, get_wraparound(nil, buckets));
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          forall_append(get_wraparound(nil, buckets), chains,
                        (upper_limit)(length(buckets)));
        }
    }
    forall_mem(nth(pindex, get_wraparound(nil, buckets)),
               get_wraparound(nil, buckets),
               (upper_limit)(length(buckets)));
    key_in_acc_then_in_hmap(get_wraparound(nil, buckets), buckets,
                            nth(pindex, get_wraparound(nil, buckets)),
                            length(buckets));
  }
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
      key_in_wraparound_then_in_hmap(buckets, k);
    } else {
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
  requires true;
  ensures mem(zero, get_just_tails(acc)) ? get_current_key_fp(acc) != none :
                                           get_current_key_fp(acc) == none;
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
  requires true == up_to(succ(i),
                         (nthProp)(buckets_get_keys_rec_fp(acc, buckets),
                                   (not_my_key)(k))) &*&
           true == mem(k, map(fst, acc)) &*&
           true == buckets_ok_rec(acc, buckets, capacity) &*&
           int_of_nat(i) < length(buckets);
  ensures true == mem(k, map(fst, get_crossing_chains_rec_fp(acc, buckets,
                                                             int_of_nat(i))));
  {
    switch(buckets) {
      case nil:
      case cons(bh,bt):
        switch(i) {
          case zero:
            next_cell_keeps_keys(acc, bh, k);
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
    switch(n) {
      case zero:
      case succ(nn):
        loop_bijection(int_of_nat(nn), capacity);
        byLoopNthPropEqNthPropUpTo(nn, lst, prop, capacity);
    }
  }//took 3m
  @*/

/*@
  lemma void upToByLoopNthPropShift1<t>(nat n, t hd, list<t> tl,
                                        fixpoint (t,bool) prop,
                                        int capacity, int start)
  requires true == up_to(n, (byLoopNthProp)(cons(hd,tl), prop,
                                            capacity, start)) &*&
           int_of_nat(n) + start <= capacity &*&
           0 < start;
  ensures true == up_to(n, (byLoopNthProp)(tl, prop, capacity, start - 1));
  {
    switch(n) {
      case zero:
      case succ(m):
        loop_bijection(start + int_of_nat(m), capacity);
        loop_bijection(start + int_of_nat(m) - 1, capacity);
        upToByLoopNthPropShift1(m, hd, tl, prop, capacity, start);
    }
  } //took 10m
  @*/

/*@
  lemma void upToNthPropShift1<t>(nat n, t hd, list<t> tl, fixpoint (t,bool) prop)
  requires true;
  ensures up_to(succ(n), (nthProp)(cons(hd, tl), prop)) ==
          (prop(hd) && up_to(n, (nthProp)(tl, prop)));
  {
    switch(n) {
      case zero:
      case succ(m):
        upToNthPropShift1(m, hd, tl, prop);
    }
  }//took 2m
  @*/

/*@
  lemma void bucket_has_then_acc_has_key<kt>(bucket<kt> b, list<pair<kt, nat> > acc, kt k)
  requires true == bucket_has_key_fp(k, b);
  ensures true == mem(k, map(fst, acc_at_this_bucket(acc, b)));
  {
    switch(b) { case bucket(chains):
      map_append(fst, acc, chains);
    }
  }//took 2m
  @*/

/*@
  lemma void crossing_chains_keep_key_hlp_inbound<kt>(list<bucket<kt> > buckets,
                                                      nat i,
                                                      int start,
                                                      int capacity,
                                                      kt k,
                                                      list<pair<kt, nat> > acc)
  requires buckets != nil &*&
           true == up_to(succ(i),
                         (byLoopNthProp)(buckets_get_keys_rec_fp(acc, buckets),
                                         (not_my_key)(k),
                                         capacity,
                                         start)) &*&
           start + int_of_nat(i) < length(buckets) &*&
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
          byLoopNthPropEqNthPropUpTo(succ(i), buckets_get_keys_rec_fp(acc, buckets),
                                     (not_my_key)(k), capacity);
          assert true == up_to(succ(i), (nthProp)(buckets_get_keys_rec_fp(acc, buckets),
                                                  (not_my_key)(k)));
          switch(i) {
            case zero:
              switch(h) { case bucket(chains):
                map_append(fst, acc, chains);
                advance_acc_preserves_key(acc_at_this_bucket(acc, h), k);
              }
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
              assert int_of_nat(i) < length(buckets);
              assert int_of_nat(n) <= length(t);
              next_i_cells_keep_keys(t, n, k, advance_acc(acc_at_this_bucket(acc, h)), capacity);
          }

        } else {
          assume(false);//TODO VF bug 68
          //upToByLoopNthPropShift1(i, get_current_key_fp(acc_at_this_bucket(acc, h)),
          //                        buckets_get_keys_rec_fp(advance_acc(acc_at_this_bucket(acc, h)), t),
          //                        (not_my_key)(k),
          //                        capacity,
          //                        start);
          //crossing_chains_keep_key_hlp_inbound(t, i, start - 1, capacity, k, advance_acc(acc_at_this_bucket(acc, h)));
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
           true == up_to(succ(i),
                         (byLoopNthProp)(buckets_get_keys_fp(buckets),
                                         (not_my_key)(k),
                                         capacity,
                                         start)) &*&
           true == bucket_has_key_fp(k, nth(start, buckets)) &*&
           0 <= start &*&
           start < length(buckets) &*&
           length(buckets) == capacity &*&
           true == buckets_ok(buckets) &*&
           start + int_of_nat(i) < capacity;
  ensures true == mem(k, map(fst, get_crossing_chains_fp(buckets, start + int_of_nat(i))));
  {
    crossing_chains_keep_key_hlp_inbound(buckets, i, start, capacity, k, get_wraparound(nil, buckets));
  }
  @*/

/*@
  lemma void
  break_down_up_to_by_loop_rec<t>(nat i, list<t> lst,
                                  int start, int capacity,
                                  fixpoint (t,bool) prop)
  requires true == up_to(i, (byLoopNthProp)(lst, prop, capacity, start)) &*&
           0 <= start &*& start < capacity &*&
           capacity <= length(lst) &*&
           capacity <= start + int_of_nat(i) &*&
           int_of_nat(i) <= capacity;
  ensures true == up_to(nat_of_int(capacity - start),
                        (byLoopNthProp)(lst, prop, capacity, start)) &*&
          true == up_to(nat_of_int(int_of_nat(i) + start - capacity),
                        (nthProp)(lst, prop));
  {
    switch(i) {
      case zero:
      case succ(n):
        assert true == (byLoopNthProp(lst, prop, capacity, start, int_of_nat(n)));
        assert true == nthProp(lst, prop, loop_fp(start + int_of_nat(n),
                                                  capacity));
        if (capacity <= start + int_of_nat(n)) {
          assert true == (start + int_of_nat(n) - capacity < capacity);
          loop_injection_n(start + int_of_nat(n) - capacity, capacity, 1);
          loop_bijection(start + int_of_nat(n) - capacity, capacity);
          break_down_up_to_by_loop_rec(n, lst, start, capacity, prop);
          assert nat_of_int(int_of_nat(succ(n)) + start - capacity) ==
                 succ(nat_of_int(int_of_nat(n) + start - capacity));
        } else {
          assert capacity == start + int_of_nat(n) + 1;
          assert nat_of_int(capacity - start) == i;
        }
    }
  }
  @*/

/*@
  lemma void break_down_up_to_by_loop<t>(list<t> lst, int i,
                                         int start, int capacity,
                                         fixpoint (t,bool) prop)
  requires capacity <= length(lst) &*&
           0 <= start &*& start < capacity &*&
           capacity <= start + i &*&
           i <= capacity &*&
           true == up_to(nat_of_int(i),
                         (byLoopNthProp)(lst, prop, capacity, start));
  ensures true == up_to(nat_of_int(capacity - start),
                        (byLoopNthProp)(lst, prop, capacity, start)) &*&
          true == up_to(nat_of_int(start + i - capacity),
                        (nthProp)(lst, prop));
  {
    break_down_up_to_by_loop_rec(nat_of_int(i), lst, start, capacity, prop);
  } //took 22m
  @*/

/*@
  lemma void crossing_chains_keep_key<kt>(list<bucket<kt> > buckets,
                                          int i,
                                          int start,
                                          int capacity,
                                          kt k)
  requires 0 <= i &*& i < capacity &*&
           0 <= start &*&
           start < length(buckets) &*&
           start + i - capacity + 1 <= capacity &*&
           buckets != nil &*&
           true == buckets_ok(buckets) &*&
           length(buckets) == capacity &*&
           true == up_to(nat_of_int(i+1),
                         (byLoopNthProp)(buckets_get_keys_fp(buckets),
                                         (not_my_key)(k),
                                         capacity,
                                         start)) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures true == mem(k, map(fst, get_crossing_chains_fp(buckets, loop_fp(start + i, capacity))));
  {
    if (capacity <= start + i) {
      buckets_keys_chns_same_len(buckets);
      break_down_up_to_by_loop(buckets_get_keys_fp(buckets),
                               i+1, start, capacity, (not_my_key)(k));
      crossing_chains_keep_key_inbound(buckets,
                                       nat_of_int(capacity - start - 1),
                                       start, capacity, k);
      wraparound_is_last_crossing_chains
        (get_wraparound(nil, buckets), buckets);
      assert get_wraparound(get_wraparound(nil, buckets), buckets) ==
             get_crossing_chains_fp(buckets, length(buckets)-1);
      assert true == mem(k, map(fst,
                                get_crossing_chains_fp
                                  (buckets,
                                    start +
                                      int_of_nat(nat_of_int(capacity -
                                                            start - 1)))));
      assert true == mem(k, map(fst, get_crossing_chains_fp
                                       (buckets, capacity - 1)));
      buckets_ok_get_wraparound_idemp(buckets);

      assert get_wraparound(nil, buckets) ==
             get_wraparound(get_wraparound(nil, buckets), buckets);
      assert get_wraparound(nil, buckets) ==
             get_crossing_chains_fp(buckets, capacity - 1);

      assert true == mem(k, map(fst, get_crossing_chains_fp(buckets,
                                                            capacity - 1)));
      assert true == mem(k, map(fst, get_wraparound
                                       (get_wraparound(nil, buckets),
                                        buckets)));

      assert true == mem(k, map(fst, get_wraparound(nil, buckets)));
      next_i_cells_keep_keys(buckets, nat_of_int(start + i - capacity),
                             k, get_wraparound(nil, buckets), capacity);
      loop_injection(start + i - capacity, capacity);
      loop_bijection(start + i - capacity, capacity);
      assert loop_fp(start + i, capacity) == (start + i - capacity);
    } else {
      crossing_chains_keep_key_inbound(buckets, nat_of_int(i),
                                       start, capacity, k);
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
           true == up_to(nat_of_int(i + 1),
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
        //@ assert true == up_to(nat_of_int(i), (byLoopNthProp)(ks, (not_my_key)(k), capacity, start));
        //@ assert true == up_to(nat_of_int(i), (byLoopNthProp)(ks, (not_my_key)(k), capacity, loop_fp(hsh(k), capacity)));
        //@ assert true == up_to(succ(nat_of_int(i)), (byLoopNthProp)(ks, (not_my_key)(k), capacity, loop_fp(hsh(k), capacity)));
        //@ assert true == up_to(nat_of_int(i+1), (byLoopNthProp)(ks, (not_my_key)(k), capacity, loop_fp(hsh(k), capacity)));
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
    //@ assert(true == not_my_key(k, nth(index, ks)));
    //@ assert(true == not_my_key(k, nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, (not_my_key)(k), start, capacity, nat_of_int(capacity));
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
  fixpoint list<int> add_partial_chain_rec_fp(list<int> chain_cnts,
                                              int start,
                                              int len) {
    switch(chain_cnts) {
      case nil:
        return nil;
      case cons(h,t):
        return (start == 0)                                         ?
                ((len == 0) ? cons(h, t) :
                  cons(h+1, add_partial_chain_rec_fp(t, 0, len-1))) :
                cons(h,add_partial_chain_rec_fp(t, start-1, len));
    }
  }

  fixpoint list<int> add_partial_chain_fp(int start,
                                          int len,
                                          list<int> chain_cnts) {
    return (length(chain_cnts) < start + len)      ?
      add_partial_chain_rec_fp
        (add_partial_chain_rec_fp
           (chain_cnts, start, len),
         0,
         len + start - length(chain_cnts)) :
      add_partial_chain_rec_fp(chain_cnts, start, len);
      }

  fixpoint nat chain_with_key_fp<kt>(list<pair<kt,nat> > chains, kt k) {
    switch(chains) {
      case nil: return zero;
      case cons(h,t):
        return switch(h) { case pair(key,len):
          return (key == k) ? len :
                    chain_with_key_fp(t, k);
        };
    }
  }

  fixpoint nat bucket_get_chain_fp<kt>(bucket<kt> b, kt k) {
    switch(b) { case bucket(chains):
      return chain_with_key_fp(chains, k);
    }
  }

  fixpoint int buckets_get_chain_fp<kt>(list<bucket<kt> > buckets,
                                        kt k,
                                        int start) {
    return int_of_nat(bucket_get_chain_fp(nth(start, buckets), k));
  }
  @*/

/*@
  lemma void buckets_remove_add_one_chain<kt>(list<bucket<kt> > buckets,
                                              int start, kt k)
  requires 0 <= start &*& start < length(buckets) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures buckets_get_chns_fp(buckets) ==
          add_partial_chain_fp
            (start, buckets_get_chain_fp(buckets, k, start),
             buckets_get_chns_fp(buckets_remove_key_fp(buckets,
                                                       k)));
  {
    assume(false);//TODO 30m
  }//took 11m and counting
  @*/

/*@
  lemma void buckets_get_chns_rec_nonneg<kt>(list<pair<kt, nat> > acc,
                                             list<bucket<kt> > buckets)
  requires true;
  ensures true == forall(buckets_get_chns_rec_fp(acc, buckets), nonneg);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_get_chns_rec_nonneg(advance_acc(acc_at_this_bucket(acc, h)), t);
    }
  }

  lemma void buckets_get_chns_nonneg<kt>(list<bucket<kt> > buckets)
  requires true;
  ensures true == forall(buckets_get_chns_fp(buckets), nonneg);
  {
    buckets_get_chns_rec_nonneg(get_wraparound(nil, buckets), buckets);
  }
  @*/

/*@
  lemma void add_part_chn_rec_still_nonneg(int start, int len,
                                           list<int> chn_cnts)
  requires true == forall(chn_cnts, nonneg);
  ensures true == forall(add_partial_chain_rec_fp(chn_cnts,
                                                  start, len),
                         nonneg);
  {
    switch(chn_cnts) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          if (len != 0) add_part_chn_rec_still_nonneg(0, len - 1, t);
        } else {
          add_part_chn_rec_still_nonneg(start - 1, len, t);
        }
    }
  }
  @*/

/*@
  lemma void add_partial_chain_rec_nonneg(int start, int len, list<int> chn_cnts)
  requires true == forall(chn_cnts, nonneg);
  ensures true == forall(add_partial_chain_rec_fp(chn_cnts, start, len), nonneg);
  {
    switch(chn_cnts) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          if (len != 0) {
            add_partial_chain_rec_nonneg(0, len - 1, t);
          }
        } else {
          add_partial_chain_rec_nonneg(start - 1, len, t);
        }
    }
  }

  lemma void add_partial_chain_nonneg(int i, int len, list<int> chn_cnts)
  requires true == forall(chn_cnts, nonneg);
  ensures true == forall(add_partial_chain_fp(i, len, chn_cnts), nonneg);
  {
    if (length(chn_cnts) < len + i) {
      add_partial_chain_rec_nonneg(i, len, chn_cnts);
      add_partial_chain_rec_nonneg(0, len + i - length(chn_cnts),
                                   add_partial_chain_rec_fp(chn_cnts, i, len));
    } else {
      add_partial_chain_rec_nonneg(i, len, chn_cnts);
    }
  }
  @*/

/*@
  lemma void add_part_chn_rec_same_len(int start, int len, list<int> chn_cnts)
  requires true;
  ensures length(chn_cnts) == length(add_partial_chain_rec_fp(chn_cnts,
                                                              start, len));
  {
    switch(chn_cnts) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          if (len != 0)
            add_part_chn_rec_same_len(0, len-1, t);
        } else {
          add_part_chn_rec_same_len(start - 1, len, t);
        }
    }
  }
  @*/

/*@
  lemma void add_part_chn_gt0_rec(int i, int len, list<int> chn_cnts)
  requires len != 0 &*& 0 <= i &*& i < length(chn_cnts) &*&
           true == forall(chn_cnts, nonneg);
  ensures 0 < nth(i, add_partial_chain_rec_fp(chn_cnts, i, len));
  {
    switch(chn_cnts) {
      case nil:
      case cons(h,t):
        if (i == 0) {
        } else {
          add_part_chn_gt0_rec(i-1, len, t);
        }
    }
  }

  lemma void add_part_chn_still_gt0_rec(int i, int start, int len,
                                        list<int> chn_cnts)
  requires 0 <= i &*& i < length(chn_cnts) &*&
           0 <= start &*& start <= i &*&
           0 < nth(i, chn_cnts) &*&
           true == forall(chn_cnts, nonneg);
  ensures 0 < nth(i, add_partial_chain_rec_fp(chn_cnts, start, len));
  {
    switch(chn_cnts) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          if (len != 0) {
            if (i != 0)
              add_part_chn_still_gt0_rec(i - 1, 0, len - 1, t);
          }
        } else {
          note(0 < start);
          add_part_chn_still_gt0_rec(i - 1, start - 1, len, t);
        }
    }
  }

  lemma void add_part_chn_gt0(int i, int len, list<int> chn_cnts)
  requires 0 <= i &*& i < length(chn_cnts) &*&
           0 < len &*&
           true == forall(chn_cnts, nonneg);
  ensures 0 < nth(i, add_partial_chain_fp(i, len, chn_cnts));
  {
    if (length(chn_cnts) < len + i) {
      add_part_chn_gt0_rec(i, len, chn_cnts);
      add_part_chn_rec_same_len(i, len, chn_cnts);
      add_part_chn_rec_still_nonneg(i, len, chn_cnts);
      add_part_chn_still_gt0_rec(i, 0, len + i - length(chn_cnts),
                                 add_partial_chain_rec_fp(chn_cnts, i, len));
    } else {
      add_part_chn_gt0_rec(i, len, chn_cnts);
    }
  }//took 80m
  @*/

/*@
  lemma void
  remove_one_cell_from_part_ch_rec(list<int> chns, int index,
                                   int len, list<int> src_chns)
  requires chns == add_partial_chain_rec_fp(src_chns,
                                            index,
                                            len) &*&
           0 <= index &*& index + 1 < length(src_chns) &*&
           0 < len;
  ensures update(index, nth(index, chns) - 1, chns) ==
          add_partial_chain_rec_fp(src_chns, index + 1, len - 1);
  {
    switch(src_chns) {
      case nil:
      case cons(h,t):
        if (index == 0) {
        } else {
          assert chns == cons(h, ?rest);
          assert rest == add_partial_chain_rec_fp(t, index - 1, len);
          remove_one_cell_from_part_ch_rec(rest, index - 1, len, t);
        }
    }
  }

  @*/

/*@
  lemma void
  add_part_chn_rec_preserves_decrement(list<int> chns, list<int> src_chns,
                                       int start, int len, int index)
  requires chns == add_partial_chain_rec_fp(src_chns, start, len) &*&
           0 <= index &*& index < length(src_chns);
  ensures update(index, nth(index, chns) - 1, chns) ==
          add_partial_chain_rec_fp(update(index,
                                          nth(index, src_chns) - 1,
                                          src_chns),
                                   start, len);
  {
    switch(src_chns) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          if (len != 0) {
            if (index != 0) {
              assert chns == cons(h+1,?rest);
              add_part_chn_rec_preserves_decrement(rest, t, 0,
                                                   len - 1, index - 1);
            }
          }
        } else {
          assert chns == cons(h,?rest);
          if (index != 0)
            add_part_chn_rec_preserves_decrement(rest, t, start - 1,
                                                 len, index - 1);
        }
    }
  }
  @*/

/*@
  lemma void dec_cancels_inc(list<int> lst, int index)
  requires 0 <= index &*& index < length(lst);
  ensures update(index, nth(index, update(index, nth(index, lst) + 1, lst)) - 1,
                 update(index, nth(index, lst) + 1, lst)) == lst;
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        if (index != 0) dec_cancels_inc(t, index - 1);
    }
  }
  @*/

/*@
  lemma void add_part_chn_rec_inc_last(list<int> chns, int len)
  requires 0 < len &*& 0 < length(chns);
  ensures add_partial_chain_rec_fp(chns, length(chns) - 1, len) ==
          update(length(chns) - 1, nth(length(chns) - 1, chns) + 1, chns);
  {
    switch(chns) {
      case nil:
      case cons(h,t):
        if (length(chns) == 1) {
          length_0_nil(t);
        } else {
          add_part_chn_rec_inc_last(t, len);
        }
    }
  }
  @*/

/*@
  lemma void add_part_chn_rec_zero_len(list<int> chns, int start)
  requires true;
  ensures add_partial_chain_rec_fp(chns, start, 0) == chns;
  {
    switch(chns) {
      case nil:
      case cons(h,t):
        if (start != 0) add_part_chn_rec_zero_len(t, start - 1);
    }
  }

  lemma void add_part_chn_zero_len(list<int> chns, int start)
  requires 0 <= start &*& start < length(chns); //optional
  ensures add_partial_chain_fp(start, 0, chns) == chns;
  {
    add_part_chn_rec_zero_len(chns, start);
  }
  @*/

/*@
  lemma void
  remove_one_cell_from_partial_chain(list<int> chns, int index,
                                     int len, list<int> src_chns,
                                     int capacity)
  requires chns == add_partial_chain_fp(index,
                                        len, src_chns) &*&
           length(src_chns) == capacity &*&
           0 <= index &*& index < capacity &*&
           0 < len &*& len <= capacity;
  ensures update(index, nth(index, chns) - 1, chns) ==
          add_partial_chain_fp(loop_fp(index + 1, capacity),
                               len - 1, src_chns);
  {
    if (index == capacity - 1) {
      loop_injection_n(index + 1 - capacity, capacity, 1);
      loop_bijection(index + 1 - capacity, capacity);
      assert loop_fp(index + 1, capacity) == 0;
      add_part_chn_rec_inc_last(src_chns, len);
      if (capacity < index + len) {
        list<int> interim = update(index, nth(index, src_chns) + 1, src_chns);
        dec_cancels_inc(src_chns, index);
        assert update(index, nth(index, interim) - 1, interim) == src_chns;
        assert add_partial_chain_rec_fp(src_chns, index, len) ==
               update(index, nth(index, src_chns) + 1, src_chns);
        add_part_chn_rec_same_len(index, len, src_chns);
        add_part_chn_rec_preserves_decrement
           (chns, update(index, nth(index, src_chns) + 1, src_chns),
            0, len + index - length(src_chns), index);
        assert chns == add_partial_chain_rec_fp(interim, 0, len + index - length(src_chns));
        assert update(index, nth(index, chns) - 1, chns) ==
               add_partial_chain_rec_fp(update(index, nth(index, interim) - 1, interim),
                                        0, len + index - length(src_chns));
        assert update(index, nth(index, chns) - 1, chns) ==
               add_partial_chain_rec_fp(src_chns,
                                        0, len + index - length(src_chns));
        assert loop_fp(index + 1, capacity) == 0;
        assert len + index - length(src_chns) == len - 1;
        assert len - 1 < capacity;
        assert add_partial_chain_rec_fp(src_chns, 0, len + index - length(src_chns)) ==
               add_partial_chain_fp(loop_fp(index + 1, capacity), len - 1, src_chns);
      } else {
        assert len == 1;
        dec_cancels_inc(src_chns, index);
        add_part_chn_rec_zero_len(src_chns, loop_fp(index + 1, capacity));
      }
    } else {
      loop_bijection(index + 1, capacity);
      assert loop_fp(index + 1, capacity) == index + 1;
      if (capacity < index + len) {
        list<int> chns0 = add_partial_chain_rec_fp(src_chns, index, len);
        remove_one_cell_from_part_ch_rec(chns0, index, len, src_chns);
        assert chns == add_partial_chain_rec_fp(chns0, 0,
                                                len + index - length(src_chns));
        add_part_chn_rec_same_len(index, len, src_chns);
        add_part_chn_rec_preserves_decrement(chns, chns0,
                                             0,
                                             len + index - length(src_chns),
                                             index);
        assert update(index, nth(index, chns) - 1, chns) ==
               add_partial_chain_rec_fp(update(index,
                                               nth(index, chns0) - 1, chns0),
                                        0,
                                        len + index - length(src_chns));
      } else {
        remove_one_cell_from_part_ch_rec(chns, index, len, src_chns);
      }
    }
  }//took 145m
  @*/

/*@
  lemma void chain_with_key_bounded<kt>(list<pair<kt,nat> > chains,
                                        kt k, int bound)
  requires true == forall(chains, (upper_limit)(bound)) &*&
           0 < bound;
  ensures int_of_nat(chain_with_key_fp(chains, k)) < bound;
  {
    switch(chains) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,len):
          if (key != k) {
            chain_with_key_bounded(t, k, bound);
          }
        }
    }
  }

  lemma void buckets_ok_rec_get_chain_bounded<kt>(list<pair<kt, nat> > acc,
                                                  list<bucket<kt> > buckets,
                                                  int bound,
                                                  kt k, int start)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           0 <= start &*& start < length(buckets) &*&
           0 < bound;
  ensures buckets_get_chain_fp(buckets, k, start) < bound;
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          switch(h) { case bucket(chains):
            forall_append(acc, chains, (upper_limit)(bound));
            assert true == forall(chains, (upper_limit)(bound));
            chain_with_key_bounded(chains, k, bound);
          }
        } else {
          buckets_ok_rec_get_chain_bounded
            (advance_acc(acc_at_this_bucket(acc, h)),
             t, bound, k, start - 1);
        }
    }
  }
  @*/
/*@
  lemma void buckets_ok_get_chain_bounded<kt>(list<bucket<kt> > buckets,
                                              kt k, int start)
  requires true == buckets_ok(buckets) &*&
           0 <= start &*& start < length(buckets);
  ensures buckets_get_chain_fp(buckets, k, start) < length(buckets) &*&
          0 <= buckets_get_chain_fp(buckets, k, start);
  {
    buckets_ok_rec_get_chain_bounded(get_wraparound(nil, buckets),
                                     buckets, length(buckets), k, start);
  }//took 25m
  @*/

/*@
  lemma void add_partial_chain_same_len(int start, int len, list<int> chns)
  requires true;
  ensures length(chns) == length(add_partial_chain_fp(start, len, chns));
  {
    if (length(chns) < len + start) {
      add_part_chn_rec_same_len(start, len, chns);
      add_part_chn_rec_same_len(0, len + start - length(chns),
                                add_partial_chain_rec_fp(chns, start, len));
    } else {
      add_part_chn_rec_same_len(start, len, chns);
    }
  }//took 3m
  @*/

/*@
  lemma void buckets_remove_key_same_len<kt>(list<bucket<kt> > buckets, kt k)
  requires true;
  ensures length(buckets_remove_key_fp(buckets, k)) == length(buckets);
  {
    switch(buckets) {
      case nil:
      case cons(bh,bt):
        switch(bh) { case bucket(chains):
          buckets_remove_key_same_len(bt,k);
        }
    }
  }//took 2m
  @*/

/*@
  lemma void acc_at_this_bucket_keeps_chain<kt>(list<pair<kt, nat> > acc,
                                                kt k, nat dst,
                                                bucket<kt> b)
  requires true == mem(pair(k,dst), acc);
  ensures true == mem(pair(k, dst), acc_at_this_bucket(acc, b));
  {
    switch(b) { case bucket(chains):
    }
  }

  lemma void advance_acc_shortens_chain<kt>(list<pair<kt, nat> > acc,
                                            kt k, nat dst)
  requires true == mem(pair(k,dst), acc) &*& dst == succ(?n);
  ensures true == mem(pair(k,n), advance_acc(acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
              advance_acc_shortens_chain(t, k, dst);
            case succ(m):
              if (h == pair(k,dst)) return;
              advance_acc_shortens_chain(t, k, dst);
          }
        }
    }
  }
  @*/

/*@
  lemma void acc_has_chain_longer<kt>(list<pair<kt, nat> > acc,
                                      list<bucket<kt> > buckets,
                                      nat dst, kt k,
                                      int i,
                                      int bound)
  requires 0 <= i &*& i < length(buckets) &*&
           nth(i, buckets_get_keys_rec_fp(acc, buckets)) != some(k) &*&
           true == buckets_ok_rec(acc, buckets, bound) &*&
           true == mem(pair(k,dst), acc);
  ensures int_of_nat(dst) != i;
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (i == 0) {
          switch(dst) {
            case zero:
              acc_at_this_bucket_keeps_chain(acc, k, dst, h);
              distinct_and_zero_this_is_the_key(acc_at_this_bucket(acc, h), k);
              assert get_current_key_fp(acc_at_this_bucket(acc, h)) == some(k);
              assert false;
            case succ(n):
              assert 0 != int_of_nat(dst);
          }
        } else {
          switch(dst) {
            case zero: return;
            case succ(n):
              acc_at_this_bucket_keeps_chain(acc, k, dst, h);
              advance_acc_shortens_chain(acc_at_this_bucket(acc, h), k, dst);
              acc_has_chain_longer(advance_acc(acc_at_this_bucket(acc, h)),
                                   t, n, k, i - 1, bound);
          }
        }
    }
  }
  @*/

/*@
  lemma void buckets_get_chain_longer_rec<kt>(list<bucket<kt> > buckets,
                                              list<pair<kt, nat> > acc,
                                              int start, int i, kt k,
                                              int bound)
  requires 0 <= i &*& start + i < length(buckets) &*&
           true == buckets_ok_rec(acc, buckets, bound) &*&
           0 <= start &*&
           nth(start + i, buckets_get_keys_rec_fp(acc, buckets)) != some(k) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures buckets_get_chain_fp(buckets, k, start) != i;
  {
    assume(false);//TODO Verifast bug: https://github.com/verifast/verifast/issues/68
    //switch(buckets) {
    //  case nil:
    //  case cons(bh,bt):
    //    if (start == 0) {
    //      nat dst = bucket_get_chain_fp(bh, k);
    //      assume(true == mem(pair(k,dst), acc_at_this_bucket(acc, bh)));
    //      acc_has_chain_longer(acc_at_this_bucket(acc, bh),
    //                           bt, dst, k, i, bound);
    //    } else {
    //      buckets_get_chain_longer_rec
    //        (bt, advance_acc(acc_at_this_bucket(acc, bh)),
    //         start - 1, i, k);
    //    }
    //}
  }
  @*/

/*@
  lemma void acc_has_long_chain_in_wraparound<kt>(list<pair<kt, nat> > acc,
                                                  list<bucket<kt> > buckets,
                                                  kt k, int dist)
  requires true == mem(pair(k,nat_of_int(dist)), acc) &*&
           length(buckets) <= dist;
  ensures true == mem(pair(k,nat_of_int(dist - length(buckets))),
                      get_wraparound(acc, buckets));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        assert 0 < dist;
        nat dn = nat_of_int(dist);
        switch(dn) {
          case zero:
            assert 0 < length(buckets);
            assert 0 < dist;
            assert int_of_nat(dn) == dist;
            assert dist == 0;
            note(dist == 0);
            note(0 < dist);
            assert false;
          case succ(n):
            acc_at_this_bucket_keeps_chain(acc, k, nat_of_int(dist), h);
            assert true == mem(pair(k,nat_of_int(dist)),
                               acc_at_this_bucket(acc, h));
            advance_acc_reduces_chain(acc_at_this_bucket(acc, h),
                                      pair(k,nat_of_int(dist)));
            assert true == mem(pair(k,n),
                               advance_acc(acc_at_this_bucket(acc, h)));
            nat m = nat_of_int(dist - 1);
            assert nat_of_int(dist - 1 + 1) == succ(m);
            assert nat_of_int(dist) == succ(m);
            assert nat_of_int(dist) == dn;
            assert succ(m) == dn;
            assert m == n;
            assert nat_of_int(dist - 1) == n;

            assert true == mem(pair(k,nat_of_int(dist - 1)),
                                    advance_acc(acc_at_this_bucket(acc, h)));
            acc_has_long_chain_in_wraparound
              (advance_acc(acc_at_this_bucket(acc, h)),
              t, k, dist - 1);

        }
    }
  }
  @*/

/*@
  lemma void bucket_has_key_in_wraparound_rec<kt>(list<bucket<kt> > buckets,
                                                  list<pair<kt, nat> > acc,
                                                  kt k, int start, int i)
  requires 0 <= start &*& start < length(buckets) &*&
           length(buckets) <= start + i &*&
           true == bucket_has_key_fp(k, nth(start, buckets)) &*&
           i == int_of_nat(bucket_get_chain_fp(nth(start, buckets), k));
  ensures true == mem(pair(k, nat_of_int(start + i - length(buckets))),
                      get_wraparound(acc, buckets));
  {
    assume(false);//TODO: VeriFast issue 68
    //switch(buckets) {
    //  case nil:
    //  case cons(h,t):
    //    if (start == 0) {
    //      acc_has_long_chain_in_wraparound(...);
    //    } else {
    //      bucket_has_key_in_wraparound_rec
    //        (t, advance_acc(acc_at_this_bucket(acc, h)), k, start - 1, i);
    //    }
    //}
  }

  lemma void bucket_has_key_in_wraparound<kt>(list<bucket<kt> > buckets,
                                              kt k, int start, int i)
  requires 0 <= start &*& start < length(buckets) &*&
           true == bucket_has_key_fp(k, nth(start, buckets)) &*&
           length(buckets) <= i + start &*&
           i == buckets_get_chain_fp(buckets, k, start) &*&
           true == buckets_ok(buckets); //this may be removed
  ensures true == mem(pair(k, nat_of_int(start + i - length(buckets))),
                      get_wraparound(nil, buckets));
  {
    bucket_has_key_in_wraparound_rec(buckets, get_wraparound(nil, buckets),
                                     k, start, i);
    buckets_ok_get_wraparound_idemp(buckets);
  }//took 110m (undone yet, VF bug on the way.)
  @*/

/*@
  lemma void buckets_get_chain_longer<kt>(list<bucket<kt> > buckets,
                                          int start, int i, kt k,
                                          int capacity)
  requires nth(loop_fp(start + i, capacity),
               buckets_get_keys_fp(buckets)) != some(k) &*&
           length(buckets) == capacity &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= i &*&
           true == bucket_has_key_fp(k, nth(start, buckets)) &*&
           true == buckets_ok(buckets);
  ensures buckets_get_chain_fp(buckets, k, start) != i;
  {
    if (start + i < capacity) {
      loop_bijection(start + i, capacity);
      buckets_get_chain_longer_rec(buckets, get_wraparound(nil, buckets),
                                   start, i, k, capacity);
    } else {
      if (capacity <= start + i - capacity) {
        assert capacity < i;
        buckets_ok_get_chain_bounded(buckets, k, start);
      } else {
        assert start + i - capacity < capacity;
        if (buckets_get_chain_fp(buckets, k, start) == i) {
          bucket_has_key_in_wraparound(buckets, k, start, i);
          assert true == mem(pair(k, nat_of_int(start + i - capacity)),
                             get_wraparound(nil, buckets));
          loop_injection_n(start + i - capacity, capacity, 1);
          loop_bijection(start + i - capacity, capacity);
          acc_has_chain_longer(get_wraparound(nil, buckets), buckets,
                              nat_of_int(start + i - capacity),
                              k, start + i - capacity,
                              capacity);
          assert false;
        }
      }
    }
  }
  @*/

/*@
  lemma void inc_modulo_loop_hlp(int a, int quotient, int capacity)
  requires 0 <= a &*& 0 < capacity &*&
           0 <= a - quotient * capacity &*&
           a - quotient * capacity < capacity;
  ensures loop_fp(loop_fp(a, capacity) + 1, capacity) ==
          loop_fp(a + 1, capacity);
  {
    int b = a - quotient * capacity;
    loop_injection_n(b, capacity, quotient);
    loop_bijection(b, capacity);
    if (b + 1 < capacity) {
      loop_injection_n(b + 1, capacity, quotient);
    } else {
      assert capacity <= b + 1;
      loop_injection_n(b + 1, capacity, quotient);
      loop_injection(0, capacity);
      loop_bijection(0, capacity);

    }
  }

  lemma void inc_modulo_loop(int a, int capacity)
  requires 0 <= a &*& 0 < capacity;
  ensures loop_fp(loop_fp(a, capacity) + 1, capacity) ==
          loop_fp(a + 1, capacity);
  {
    int quotient = a / capacity;
    div_rem(a, capacity);
    inc_modulo_loop_hlp(a, a/capacity, capacity);
  }//took 30m
  @*/

/*@
  lemma void buckets_chain_end_rec<kt>(list<pair<kt, nat> > acc,
                                       list<bucket<kt> > buckets,
                                       kt k, int start, int i,
                                       int capacity)
  requires nth(start + i, buckets_get_keys_rec_fp(acc, buckets)) ==
           some(k) &*&
           0 < capacity &*&
           0 <= start &*&
           0 <= i &*&
           length(buckets) <= capacity &*&
           start + i < length(buckets) &*&
           true == buckets_ok_rec(acc, buckets, capacity) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures buckets_get_chain_fp(buckets, k, start) == i;
  {
    assume(false);//TODO VF issue 68
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          assume(false);//TODO
        } else {
          buckets_chin_end_rec(advance_acc(acc_at_this_bucket(acc, h)),
                               t, k, start - 1, i, capacity);
        }
    }
  }

  lemma void buckets_chain_end<kt>(list<bucket<kt> > buckets, kt k,
                                   int start, int i, int capacity)
  requires nth(loop_fp(start + i, capacity), buckets_get_keys_fp(buckets)) ==
           some(k) &*&
           0 < capacity &*& length(buckets) == capacity &*&
           true == buckets_ok(buckets) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures buckets_get_chain_fp(buckets, k, start) == i;
  {
    assume(false);//TODO see the rec version
  }
  @*/

/*@
  lemma void chns_after_partial_chain_ended<kt>(list<bucket<kt> > buckets, kt k,
                                                int start, int i,
                                                int capacity)
  requires nth(loop_fp(start + i, capacity), buckets_get_keys_fp(buckets)) ==
           some(k) &*&
           length(buckets) == capacity &*& 0 < capacity &*&
           true == buckets_ok(buckets) &*&
           true == bucket_has_key_fp(k, nth(start, buckets));
  ensures buckets_get_chns_fp(buckets_remove_key_fp(buckets, k)) ==
          add_partial_chain_fp
            (loop_fp(start + i, capacity),
             buckets_get_chain_fp(buckets, k, start) - i,
             buckets_get_chns_fp(buckets_remove_key_fp(buckets,
                                                       k)));
  {
    buckets_chain_end(buckets, k, start, i, capacity);
    assert buckets_get_chain_fp(buckets, k, start) == i;
    loop_lims(start + i, capacity);
    buckets_remove_key_same_len(buckets, k);
    buckets_keys_chns_same_len(buckets_remove_key_fp(buckets, k));
    add_part_chn_zero_len
      (buckets_get_chns_fp(buckets_remove_key_fp(buckets, k)),
       loop_fp(start + i, capacity));
  } //took 25m, undone: VF issue 68.
  @*/

/*@
  lemma void nonmem_map_append_filter<t1,t2>(fixpoint (t1,t2) f1,
                                             fixpoint (t1,bool) f2,
                                             list<t1> l,
                                             list<t1> l2,
                                             t1 el)
  requires false == mem(f1(el), map(f1, append(l, l2)));
  ensures false == mem(f1(el), map(f1, append(l, filter(f2, l2))));
  {
    switch(l) {
      case nil:
        nonmem_map_filter(f1, f2, l2, el);
      case cons(h,t):
        nonmem_map_append_filter(f1, f2, t, l2, el);
    }
  }

  lemma void distinct_map_append_filter<t1,t2>(fixpoint (t1,t2) f1,
                                               fixpoint (t1,bool) f2,
                                               list<t1> l1,
                                               list<t1> l2)
  requires true == distinct(map(f1, append(l1, l2)));
  ensures true == distinct(map(f1, append(l1, filter(f2, l2))));
  {
    switch(l1) {
      case nil:
        distinct_map_filter(f1, f2, l2);
      case cons(h,t):
        distinct_map_append_filter(f1, f2, t, l2);
        assert true == distinct(map(f1, append(t, filter(f2, l2))));
        assert false == mem(f1(h), map(f1, append(t, l2)));
        nonmem_map_append_filter(f1, f2, t, l2, h);
        assert false == mem(f1(h), map(f1, append(t, filter(f2, l2))));
    }
  }

  @*/

/*@
  lemma void advance_acc_dec_nonmem<kt>(nat n, list<pair<kt, nat> > acc)
  requires false == mem(succ(n), get_just_tails(acc));
  ensures false == mem(n, get_just_tails(advance_acc(acc)));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
            case succ(m):
          }
          advance_acc_dec_nonmem(n, t);
        }
    }
  }
  @*/

/*@
  lemma void advance_acc_still_distinct<kt>(list<pair<kt, nat> > acc)
  requires true == distinct(get_just_tails(acc));
  ensures true == distinct(get_just_tails(advance_acc(acc)));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
            case succ(n):
              advance_acc_dec_nonmem(n, t);
              assert false == mem(n, get_just_tails(advance_acc(t)));
          }
          advance_acc_still_distinct(t);
        }
    }
  }
  @*/


/*@
  lemma void buckets_ok_rec_acc_tails_distinct<kt>(list<pair<kt, nat> > acc,
                                                   list<bucket<kt> > buckets,
                                                   int bound)
  requires true == buckets_ok_rec(acc, buckets, bound);
  ensures true == distinct(get_just_tails(acc));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          map_append(snd, acc, chains);
          distinct_unappend(get_just_tails(acc), get_just_tails(chains));
        }
    }
  }
  @*/


/*@
  lemma void acc_subset_buckets_still_ok_rec<kt>(list<pair<kt, nat> > acc1,
                                                 list<pair<kt, nat> > acc2,
                                                 list<bucket<kt> > buckets,
                                                 int bound)
  requires true == subset(acc1, acc2) &*&
           true == distinct(get_just_tails(acc1)) &*&
           true == buckets_ok_rec(acc2, buckets, bound);
  ensures true == buckets_ok_rec(acc1, buckets, bound);
  {
    switch(buckets) {
      case nil:
        assert true == distinct(get_just_tails(acc1));
        subset_forall(acc1, acc2, (upper_limit)(bound - 1));
      case cons(h,t):
        acc_at_this_bucket_subset(acc1, acc2, h);
        assert true == subset(acc_at_this_bucket(acc1, h),
                              acc_at_this_bucket(acc2, h));
        advance_acc_subset(acc_at_this_bucket(acc1, h),
                           acc_at_this_bucket(acc2, h));
        assert true == subset(advance_acc(acc_at_this_bucket(acc1, h)),
                              advance_acc(acc_at_this_bucket(acc2, h)));
        switch(h) { case bucket(chains):
          map_append(snd, acc2, chains);
          assert true == distinct(append(get_just_tails(acc2),
                                         get_just_tails(chains)));
          subset_map(acc1, acc2, snd);
          subset_append_distinct(get_just_tails(acc1),
                                 get_just_tails(acc2),
                                 get_just_tails(chains));
          map_append(snd, acc1, chains);
          assert true == distinct(get_just_tails(append(acc1, chains)));
        }
        assert true == distinct(get_just_tails(acc_at_this_bucket(acc2, h)));
        assert true == distinct(get_just_tails(acc_at_this_bucket(acc1, h)));
        subset_forall(acc_at_this_bucket(acc1, h),
                      acc_at_this_bucket(acc2, h), (upper_limit)(bound));
        advance_acc_still_distinct(acc_at_this_bucket(acc1, h));
        acc_subset_buckets_still_ok_rec
          (advance_acc(acc_at_this_bucket(acc1, h)),
           advance_acc(acc_at_this_bucket(acc2, h)),
           t, bound);

    }
  }
  @*/

/*@
  lemma void buckets_remove_key_still_ok_rec<kt>(list<pair<kt, nat> > acc,
                                                 list<bucket<kt> > buckets,
                                                 kt k,
                                                 int bound)
  requires true == buckets_ok_rec(acc, buckets, bound);
  ensures true == buckets_ok_rec(acc, buckets_remove_key_fp(buckets, k), bound);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > new_acc_atb =
            append(acc, filter((not_this_key_pair_fp)(k), chains));
          filter_subset((not_this_key_pair_fp)(k), chains);
          append_both_subset(filter((not_this_key_pair_fp)(k), chains),
                             acc, chains);
          assert true == subset(new_acc_atb, acc_atb);
          advance_acc_subset(new_acc_atb, acc_atb);
          assert true == subset(advance_acc(new_acc_atb) ,
                                advance_acc(acc_atb));
          distinct_map_append_filter(snd, (not_this_key_pair_fp)(k),
                                     acc, chains);
          assert true == distinct(get_just_tails(new_acc_atb));
          subset_forall(new_acc_atb, acc_atb, (upper_limit)(bound));
          assert true == forall(new_acc_atb, (upper_limit)(bound));
          assert true == buckets_ok_rec(advance_acc(acc_atb), t, bound);
          advance_acc_still_distinct(new_acc_atb);
          acc_subset_buckets_still_ok_rec(advance_acc(new_acc_atb),
                                          advance_acc(acc_atb),
                                          t,
                                          bound);
          assert true == buckets_ok_rec(advance_acc(new_acc_atb), t, bound);
          buckets_remove_key_still_ok_rec(advance_acc(new_acc_atb),
                                          t, k, bound);
        }
    }
  }
  @*/

/*@
  lemma void filter_acc_at_this_b_idemp<kt>(list<pair<kt, nat> > acc,
                                            list<pair<kt, nat> > chns,
                                            fixpoint (pair<kt, nat>, bool) f)
  requires true;
  ensures filter(f, acc_at_this_bucket(acc, bucket(chns))) ==
          acc_at_this_bucket(filter(f, acc), bucket(filter(f, chns)));
  {
    filter_append_idemp(acc, chns, f);
  }
  @*/

/*@
  lemma void remkey_advance_acc_idemp<kt>(list<pair<kt, nat> > acc,
                                          kt k)
  requires true;
  ensures filter((not_this_key_pair_fp)(k), advance_acc(acc)) ==
          advance_acc(filter((not_this_key_pair_fp)(k), acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        remkey_advance_acc_idemp(t, k);
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
        }
    }
  }
  @*/

/*@
  lemma void get_wraparound_removed_key<kt>(list<pair<kt, nat> > acc,
                                            list<bucket<kt> > buckets,
                                            kt k)
  requires true;
  ensures get_wraparound(filter((not_this_key_pair_fp)(k), acc),
                         buckets_remove_key_fp(buckets, k)) ==
          filter((not_this_key_pair_fp)(k), get_wraparound(acc, buckets));
  {
    switch(buckets) {
      case nil:
        assert nil == buckets_remove_key_fp(buckets, k);
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > new_chains = filter((not_this_key_pair_fp)(k), chains);
          bucket<kt> new_h = bucket(new_chains);
          get_wraparound_removed_key(advance_acc(acc_at_this_bucket(acc, h)),
                                     t, k);
          filter_acc_at_this_b_idemp(acc, chains, (not_this_key_pair_fp)(k));
          remkey_advance_acc_idemp(acc_at_this_bucket(acc, h), k);
        }
    }
  }
  @*/

/*@
  lemma void buckets_ok_rec_wraparound_distinct<kt>(list<pair<kt, nat> > acc,
                                                    list<bucket<kt> > buckets,
                                                    int bound)
  requires true == buckets_ok_rec(acc, buckets, bound);
  ensures true == distinct(get_just_tails(get_wraparound(acc, buckets)));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_ok_rec_wraparound_distinct
          (advance_acc(acc_at_this_bucket(acc, h)),
           t, bound);
    }
  }
  @*/

/*@
  lemma void acc_remove_key_buckets_still_ok_rec<kt>(list<pair<kt, nat> > acc,
                                                     list<bucket<kt> > buckets,
                                                     kt k, int bound)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           true == distinct(get_just_tails(acc));
  ensures true == buckets_ok_rec(filter((not_this_key_pair_fp)(k), acc),
                                 buckets, bound);
  {
    filter_subset((not_this_key_pair_fp)(k), acc);
    distinct_map_filter(snd, (not_this_key_pair_fp)(k), acc);
    acc_subset_buckets_still_ok_rec(filter((not_this_key_pair_fp)(k), acc),
                                    acc, buckets, bound);
  }
  @*/
/*@
  lemma void buckets_remove_key_still_ok<kt>(list<bucket<kt> > buckets, kt k)
  requires true == buckets_ok(buckets);
  ensures true == buckets_ok(buckets_remove_key_fp(buckets, k));
  {
    if (buckets == nil) {
      return;
    }
    buckets_remove_key_same_len(buckets, k);
    buckets_remove_key_still_ok_rec(get_wraparound(nil, buckets), buckets,
                                    k, length(buckets));
    get_wraparound_removed_key(nil, buckets, k);
    buckets_ok_rec_wraparound_distinct(get_wraparound(nil, buckets),
                                       buckets, length(buckets));
    buckets_ok_get_wraparound_idemp(buckets);
    acc_remove_key_buckets_still_ok_rec(get_wraparound(nil, buckets),
                                        buckets_remove_key_fp(buckets, k),
                                        k, length(buckets));
  } //took 225m
  @*/

/*@
  lemma void nonmem_not_this_key<kt>(list<pair<kt, nat> > acc, kt k)
  requires false == mem(k, map(fst, acc));
  ensures true == forall(acc, (not_this_key_pair_fp)(k));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        nonmem_not_this_key(t, k);
    }
  }
  @*/

/*@
  lemma void current_key_is_mem<kt>(list<pair<kt, nat> > acc, kt k)
  requires get_current_key_fp(acc) == some(k);
  ensures true == mem(k, map(fst, acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
              current_key_is_mem(t, k);
          }
        }
    }
  }
  @*/

/*@
  lemma void advance_acc_filter_current_key<kt>(list<pair<kt, nat> > acc,
                                                kt k)
  requires true == distinct(map(fst, acc)) &*&
           get_current_key_fp(acc) == some(k);
  ensures advance_acc(acc) ==
          advance_acc(filter((not_this_key_pair_fp)(k), acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
              nonmem_not_this_key(t, k);
              filter_forall((not_this_key_pair_fp)(k), t);
            case succ(n):
              advance_acc_filter_current_key(t, k);
              current_key_is_mem(t, k);
          }
        }
    }
  } //took 25m
  @*/

/*@
  fixpoint bool keys_contain_keys<kt>(list<option<kt> > ks1, list<option<kt> > ks2) {
    switch(ks1) {
      case nil: return ks2 == nil;
      case cons(h,t): return switch(h) {
        case none:
          return keys_contain_keys(t, tail(ks2));
        case some(k):
          return head(ks2) == some(k) &&
                 keys_contain_keys(t, tail(ks2));
      };
    }
  }
  @*/

/*@
  lemma void keys_contain_keys_nodups<kt>(list<option<kt> > ks1, list<option<kt> > ks2)
  requires true == keys_contain_keys(ks1, ks2) &*& true == no_dups(ks2);
  ensures true == no_dups(ks1);
  {
    assume(false);//TODO 10m
  }
  @*/

/*@
  lemma void dups_in_acc_dups_in_keys<kt>(list<pair<kt, nat> > acc,
                                          list<bucket<kt> > buckets,
                                          int bound)
  requires false == distinct(map(fst, acc)) &*&
           //true == distinct(map(snd, acc)) &*& should follow from buckets_ok
           true == buckets_ok_rec(acc, buckets, bound);
           //true == forall(acc, (upper_limit)(length(buckets)));  also
  ensures false == no_dups(buckets_get_keys_rec_fp(acc, buckets));
  {
    switch(buckets) {
      case nil:
        assume(false);//TODO (fst distinct is false -> acc has 2 elems, snd distinct is true -> the dists are not all 0, -> length(buckets) is more than zero
      case cons(h,t):
        list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > acc_atb_bnd =
            append(acc, filter((upper_limit)(length(buckets)),
                               chains));
          filter_forall((upper_limit)(length(buckets)), chains);
          forall_append(acc, filter((upper_limit)(length(buckets)), chains),
                        (upper_limit)(length(buckets)));
          assert true == forall(filter((upper_limit)(length(buckets)), chains),
                                (upper_limit)(length(buckets)));
          assume(forall(acc_atb_bnd, (upper_limit)(length(buckets))));//TODO
          assert true == forall(acc_atb_bnd, (upper_limit)(length(buckets)));
          assume( false == distinct(map(fst, acc_atb_bnd)));//TODO
          assert false == distinct(map(fst, acc_atb_bnd));
          assume( true == subset(acc_atb_bnd, acc_atb));//TODO
          assert true == subset(acc_atb_bnd, acc_atb);
          advance_acc_subset(acc_atb_bnd, acc_atb);
          assert true == subset(advance_acc(acc_atb_bnd), advance_acc(acc_atb));
          assume( keys_contain_keys(buckets_get_keys_rec_fp(advance_acc(acc_atb_bnd), t),
                                   buckets_get_keys_rec_fp(advance_acc(acc_atb), t))); //TODO
          assert true == keys_contain_keys(buckets_get_keys_rec_fp(advance_acc(acc_atb_bnd), t),
                                           buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
          option<kt> ck = get_current_key_fp(acc_atb_bnd);
          switch(ck) {
            case none:
              assume( false == distinct(map(fst, advance_acc(acc_atb_bnd))));//TODO
              assert false == distinct(map(fst, advance_acc(acc_atb_bnd)));
            case some(k):
              assume( get_current_key_fp(acc_atb) == some(k));//TODO
              assert get_current_key_fp(acc_atb) == some(k);
              if (mem(k, map(fst, acc_atb_bnd))) {
                assume( true == mem(some(k), buckets_get_keys_rec_fp(advance_acc(acc_atb_bnd), t)));//TODO
                assert true == mem(some(k), buckets_get_keys_rec_fp(advance_acc(acc_atb_bnd), t));
                assume( true == mem(some(k), buckets_get_keys_rec_fp(advance_acc(acc_atb), t)));//TODO
                assert true == mem(some(k), buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
                list<option<kt> > kss = buckets_get_keys_rec_fp(acc, buckets);
                assert kss == cons(some(k), buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
                assert false == no_dups(buckets_get_keys_rec_fp(acc, buckets));
                return;
              } else {
                assume( false == distinct(map(fst, advance_acc(acc_atb_bnd))));//TODO
                assert false == distinct(map(fst, advance_acc(acc_atb_bnd)));
              }
          }
          assert true == distinct(map(snd, acc_atb));
          assume(true == distinct(map(snd, acc_atb_bnd)));//TODO
          assert true == distinct(map(snd, acc_atb_bnd));
          assume(true == distinct(map(snd, advance_acc(acc_atb_bnd))));//TODO
          assert true == distinct(map(snd, advance_acc(acc_atb_bnd)));
          acc_subset_buckets_still_ok_rec(advance_acc(acc_atb_bnd), advance_acc(acc_atb), t, bound);
          assert true == forall(acc_atb_bnd, (upper_limit)(length(buckets)));
          advance_acc_lower_limit(acc_atb_bnd, length(buckets));
          assert true == forall(advance_acc(acc_atb_bnd), (upper_limit)(length(t)));
          dups_in_acc_dups_in_keys(advance_acc(acc_atb_bnd), t, bound);
          assert false == no_dups(buckets_get_keys_rec_fp(advance_acc(acc_atb_bnd), t));
          if (no_dups(buckets_get_keys_rec_fp(advance_acc(acc_atb), t))) {
            keys_contain_keys_nodups(buckets_get_keys_rec_fp(advance_acc(acc_atb_bnd), t),
                                     buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
          }
          assert false == no_dups(buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
        }
    }
  }
  @*/

/*@
  lemma void dup_survives_buckets_get_keys<kt>(list<pair<kt, nat> > acc,
                                               list<bucket<kt> > buckets,
                                               int bound)
  requires false == distinct(map(fst, acc)) &*&
           true == distinct(map(snd, acc)) &*&
           true == buckets_ok_rec(acc, buckets, bound);
  ensures false == distinct(map(fst, get_wraparound(acc, buckets))) ||
          false == no_dups(buckets_get_keys_rec_fp(acc, buckets));
  {
    switch(buckets) {
      case nil:
        assert get_wraparound(acc, buckets) == acc;
        assert false == distinct(map(fst, get_wraparound(acc, buckets)));
      case cons(h,t):
        switch(h) { case bucket(chains) :
          list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
          assume(false == distinct(map(fst, acc_atb))); //TODO
          assert false == distinct(map(fst, acc_atb));
          option<kt> ck = get_current_key_fp(acc_atb);
          switch(ck) {
            case none:
              assume(false == distinct(map(fst, advance_acc(acc_atb))));//TODO
              assert false == distinct(map(fst, advance_acc(acc_atb)));
            case some(k):
              if (mem(k, map(fst, advance_acc(acc)))) {

                assume(mem(some(k), buckets_get_keys_rec_fp
                                      (advance_acc(acc_atb), t)));//TODO
                assert true == mem(some(k), buckets_get_keys_rec_fp
                                              (advance_acc(acc_atb), t));
                assert false == no_dups(buckets_get_keys_rec_fp(acc, buckets));
                return;
              } else {
                assume(false == distinct(map(fst, advance_acc(acc_atb))));//TODO
                assert false == distinct(map(fst, advance_acc(acc_atb)));
              }
          }
          assert true == distinct(map(snd, acc_atb));
          assume(true == distinct(map(snd, advance_acc(acc_atb))));//TODO
          assert true == distinct(map(snd, advance_acc(acc_atb)));
          dup_survives_buckets_get_keys(advance_acc(acc_atb), t, bound);

        }
    }
  }
  @*/

/*@
  lemma void acc_rm_key_buckets_get_keys_rec<kt>(list<pair<kt, nat> > acc,
                                                 list<bucket<kt> > buckets,
                                                 list<option<kt> > keys,
                                                 kt k, int bound)
  requires true == mem(some(k), keys) &*&
           true == no_dups(keys) &*&
           true == buckets_ok_rec(acc, buckets, bound) &*&
           true == distinct(map(fst, acc)) &*&
           keys == buckets_get_keys_rec_fp(acc, buckets) &*&
           true == distinct(map(fst, get_wraparound(acc, buckets))) &*&
           true;//false == exists(buckets, (bucket_has_key_fp)(k)); -- something more elaborate, like does not exist only among non-wrappingaround chains
  ensures buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k), acc),
                                  buckets) ==
          update(index_of(some(k), keys), none, keys);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
          assert keys == cons(get_current_key_fp(acc_atb), ?kt);
          if (get_current_key_fp(acc_atb) == some(k)) {
            assert false == mem(some(k), kt);
            assert index_of(some(k), keys) == 0;
            assert update(index_of(some(k), keys), none, keys) == cons(none, kt);
            //TODO 100m
            //if (!distinct(map(fst, advance_acc(acc_atb)))) {
            //  assert true == distinct(map(snd, acc_atb));
            //  assume(true == distinct(map(snd, advance_acc(acc_atb))));
            //  assert true == distinct(map(snd, advance_acc(acc_atb)));
            //  dup_survives_buckets_get_keys(advance_acc(acc_atb), t, bound);
            //  assert false;
            //}
            //assert true == distinct(map(fst, advance_acc(acc_atb)));
            //advance_acc_filter_current_key(acc_atb, k);
            assume(false == mem(k, map(fst, advance_acc(acc_atb)))); //TODO
            assert false == mem(k, map(fst, advance_acc(acc_atb)));
            assume(advance_acc(acc_atb) ==
                   filter((not_this_key_pair_fp)(k), advance_acc(acc_atb)));//TODO
            assert advance_acc(acc_atb) ==
                   filter((not_this_key_pair_fp)(k), advance_acc(acc_atb));
            assert buckets_get_keys_rec_fp
                     (filter((not_this_key_pair_fp)(k),
                             advance_acc(acc_atb)), t) ==
                   buckets_get_keys_rec_fp(advance_acc(acc_atb), t);
            assume( filter((not_this_key_pair_fp)(k), advance_acc(acc_atb)) ==
                   advance_acc(append(filter((not_this_key_pair_fp)(k), acc), chains)));//TODO
            assert filter((not_this_key_pair_fp)(k), advance_acc(acc_atb)) ==
                   advance_acc(append(filter((not_this_key_pair_fp)(k), acc), chains));
            assert get_current_key_fp(acc_atb) == some(k);
            assume( get_current_key_fp(filter((not_this_key_pair_fp)(k), acc_atb)) == none);//TODO
            assert get_current_key_fp(filter((not_this_key_pair_fp)(k), acc_atb)) == none;
            assume (get_current_key_fp(append(filter((not_this_key_pair_fp)(k), acc), chains)) == none);//TODO
            assert get_current_key_fp(append(filter((not_this_key_pair_fp)(k), acc), chains)) == none;
            assert buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k), acc), buckets) ==
                   cons(none, buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
            assert keys == cons(some(k), buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
            assert update(index_of(some(k), keys), none, keys) ==
                   cons(none, buckets_get_keys_rec_fp(advance_acc(acc_atb), t));
            return;
          } else {
            if (!distinct(map(fst, advance_acc(acc_atb)))) {
              assert true == distinct(map(snd, acc_atb));
              assume(true == distinct(map(snd, advance_acc(acc_atb))));
              assert true == distinct(map(snd, advance_acc(acc_atb)));
              dup_survives_buckets_get_keys(advance_acc(acc_atb), t, bound);
              assert false;
            }
            acc_rm_key_buckets_get_keys_rec
              (advance_acc(acc_atb), t, tail(keys), k, bound);
            assume(filter((not_this_key_pair_fp)(k), advance_acc(acc_atb)) ==
              advance_acc(append(filter((not_this_key_pair_fp)(k), acc), chains)));//TODO
            assert filter((not_this_key_pair_fp)(k), advance_acc(acc_atb)) ==
                   advance_acc(append(filter((not_this_key_pair_fp)(k), acc), chains));
            assume(get_current_key_fp(acc_atb) ==
                   get_current_key_fp(advance_acc(acc_at_this_bucket(filter((not_this_key_pair_fp)(k), acc), h))));
            assert get_current_key_fp(acc_atb) ==
                   get_current_key_fp(advance_acc(acc_at_this_bucket(filter((not_this_key_pair_fp)(k), acc), h)));
            assume(false);//TODO
            assert buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k), acc), buckets) ==
                   cons(get_current_key_fp(acc_atb),
                        buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k), advance_acc(acc_atb)), t));
          }
        }
    }
  }//took 25m + 20m + 30m
  @*/

/*@
  lemma void buckets_rm_key_get_keys_rec<kt>(list<pair<kt, nat> > acc,
                                             list<bucket<kt> > buckets,
                                             list<option<kt> > keys,
                                             kt k)
  requires true == mem(some(k), keys) &*&
           true == no_dups(keys) &*&
           keys == buckets_get_keys_rec_fp(acc, buckets) &*&
           true == forall(acc, (not_this_key_pair_fp)(k));
  ensures buckets_get_keys_rec_fp(acc, buckets_remove_key_fp(buckets, k)) ==
          update(index_of(some(k), keys), none, keys);
  {
    assume(false);//TODO 30m
  }
  @*/

/*@
  lemma void buckets_rm_key_get_keys<kt>(list<bucket<kt> > buckets,
                                         kt k)
  requires true == mem(some(k), buckets_get_keys_fp(buckets)) &*&
           true == no_dups(buckets_get_keys_fp(buckets)) &*&
           true == buckets_ok(buckets);
  ensures buckets_get_keys_fp(buckets_remove_key_fp(buckets, k)) ==
          update(index_of(some(k), buckets_get_keys_fp(buckets)),
                 none, buckets_get_keys_fp(buckets));
  {
    if (forall(get_wraparound(nil, buckets), (not_this_key_pair_fp)(k))) {
      assume(get_wraparound(nil, buckets) ==
             get_wraparound(nil, buckets_remove_key_fp(buckets, k))); //TODO
      assert get_wraparound(nil, buckets) ==
             get_wraparound(nil, buckets_remove_key_fp(buckets, k));
      buckets_rm_key_get_keys_rec(get_wraparound(nil, buckets), buckets,
                                  buckets_get_keys_fp(buckets), k);
    } else {
      if (!distinct(map(fst, get_wraparound(nil, buckets)))) {
        dups_in_acc_dups_in_keys(get_wraparound(nil, buckets), buckets,
                                 length(buckets));
      }
      buckets_ok_get_wraparound_idemp(buckets);
      acc_rm_key_buckets_get_keys_rec(get_wraparound(nil, buckets),
                                      buckets,
                                      buckets_get_keys_fp(buckets),
                                      k, length(buckets));
      assume(get_wraparound(nil, buckets_remove_key_fp(buckets, k)) ==
             filter((not_this_key_pair_fp)(k), get_wraparound(nil, buckets)));//TODO
      assert get_wraparound(nil, buckets_remove_key_fp(buckets, k)) ==
             filter((not_this_key_pair_fp)(k), get_wraparound(nil, buckets));
      assume(buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k), get_wraparound(nil, buckets)), buckets) ==
             buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k), get_wraparound(nil, buckets)), buckets_remove_key_fp(buckets, k)));//TODO
      assert buckets_get_keys_fp(buckets_remove_key_fp(buckets, k)) ==
             buckets_get_keys_rec_fp(filter((not_this_key_pair_fp)(k),
                                            get_wraparound(nil, buckets)),
                                     buckets);
    }
  }//took 60m + 40m so far
  //TODO 300m
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
    //@ assert(true == not_my_key(k, nth(index, ks)));
    //@ assert(true == not_my_key(k, nth(loop_fp(i+start,capacity), ks)));
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
  fixpoint bool less_than(int lim, nat x) { return int_of_nat(x) < lim; }

  lemma void upper_bound_less_than<kt>(list<pair<kt, nat> > acc, int lim)
  requires true;
  ensures forall(acc, (upper_limit)(lim)) ==
          forall(get_just_tails(acc), (less_than)(lim));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        upper_bound_less_than(t, lim);
    }
  }

  lemma void less_and_not_eq_lesser(nat x, nat lim)
  requires int_of_nat(x) < int_of_nat(succ(lim)) &*&
           x != lim;
  ensures int_of_nat(x) < int_of_nat(lim);
  {
    switch(x) {
      case zero:
        switch(lim) {
          case zero:
          case succ(ln):
        }
      case succ(xn):
        switch(lim) {
          case zero:
          case succ(ln):
            less_and_not_eq_lesser(xn,ln);
        }
    }
  }

  lemma void less_than_not_eq_upper_lesser(list<nat> tails, nat lim)
  requires true == forall(tails, (less_than)(int_of_nat(succ(lim)))) &*&
           false == mem(lim, tails);
  ensures true == forall(tails, (less_than)(int_of_nat(lim)));
  {
    switch(tails) {
      case nil:
      case cons(h,t):
        assert int_of_nat(h) < int_of_nat(succ(lim));
        assert h != lim;
        less_and_not_eq_lesser(h, lim);
        assert int_of_nat(h) < int_of_nat(lim);
        less_than_not_eq_upper_lesser(t, lim);
    }
  }

  lemma void less_than_remove_big(list<nat> tails, nat lim)
  requires true == forall(tails, (less_than)(int_of_nat(succ(lim)))) &*&
           true == distinct(tails);
  ensures true == forall(remove(lim, tails), (less_than)(int_of_nat(lim)));
  {
    switch(tails) {
      case nil:
      case cons(h,t):
        if (h == lim) {
          assert false == mem(lim, t);
          assert true == forall(t, (less_than)(int_of_nat(succ(lim))));
          less_than_not_eq_upper_lesser(t, lim);
          assert true == forall(t, (less_than)(int_of_nat(lim)));
        } else {
          less_than_remove_big(t, lim);
          less_and_not_eq_lesser(h, lim);
        }
    }
  }

  lemma void less_than_distinct_few_rec(list<nat> tails, nat lim)
  requires true == forall(tails, (less_than)(int_of_nat(lim))) &*&
           true == distinct(tails);
  ensures length(tails) <= int_of_nat(lim);
  {
    switch(lim) {
      case zero:
        switch(tails) {
          case nil:
          case cons(h,t):
            assert int_of_nat(h) < 0;
            assert false;
        };
      case succ(n):
        if (mem(n, tails)) {
          assert length(remove(n, tails)) + 1 == length(tails);
        } else {
          assert length(remove(n, tails)) == length(tails);
        }
        less_than_remove_big(tails, n);
        distinct_remove(n, tails);
        less_than_distinct_few_rec(remove(n, tails), n);
    }
  }

  lemma void less_than_distinct_few(list<nat> tails, int lim)
  requires true == forall(tails, (less_than)(lim)) &*&
           true == distinct(tails) &*&
           0 <= lim;
  ensures length(tails) <= lim;
  {
    assert true == forall(tails, (less_than)(lim));
    assert lim == int_of_nat(nat_of_int(lim));
    assert true == forall(tails, (less_than)(int_of_nat(nat_of_int(lim))));
    less_than_distinct_few_rec(tails, nat_of_int(lim));
  }
  @*/


/*@
  lemma void buckets_ok_chn_bound_rec<kt>(list<pair<kt, nat> > acc,
                                          list<bucket<kt> > buckets,
                                          int i,
                                          int bound)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           0 <= i &*& i < length(buckets) &*&
           0 < bound;
  ensures length(buckets_get_chns_rec_fp(acc, buckets)) == length(buckets) &*&
          0 <= nth(i, buckets_get_chns_rec_fp(acc, buckets)) &*&
          nth(i, buckets_get_chns_rec_fp(acc, buckets)) <= bound - 1;
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_keys_chns_same_len_rec(acc, buckets);
        list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
        if (i == 0) {
          assert nth(i, buckets_get_chns_rec_fp(acc, buckets)) ==
                 length(advance_acc(acc_atb));
          assert 0 <= length(advance_acc(acc_atb));
          advance_acc_lower_limit(acc_atb, bound);
          list<nat> tails = get_just_tails(advance_acc(acc_atb));
          map_preserves_length(snd, advance_acc(acc_atb));
          assert length(advance_acc(acc_atb)) == length(tails);
          assert true == forall(advance_acc(acc_atb), (upper_limit)(bound - 1));
          upper_bound_less_than(advance_acc(acc_atb), bound - 1);
          assert true == forall(tails, (less_than)(bound - 1));
          advance_acc_still_distinct(acc_atb);
          assert true == distinct(tails);
          less_than_distinct_few(tails, bound - 1);
          assert length(advance_acc(acc_atb)) <= bound - 1;
        } else {
          buckets_ok_chn_bound_rec(advance_acc(acc_atb), t, i - 1, bound);
        }
    }
  }
  @*/

/*@
  lemma void buckets_ok_chn_bound<kt>(list<bucket<kt> > buckets,
                                      int i)
  requires true == buckets_ok(buckets) &*& 0 <= i &*& i < length(buckets);
  ensures length(buckets_get_chns_fp(buckets)) == length(buckets) &*&
          0 <= nth(i, buckets_get_chns_fp(buckets)) &*&
          nth(i, buckets_get_chns_fp(buckets)) <= length(buckets);
  {
    buckets_ok_chn_bound_rec(get_wraparound(nil, buckets), buckets,
                             i, length(buckets));
  }//took 40m
  @*/

/*@
  lemma void gt_zero_neq_zero(int x)
  requires 0 < x;
  ensures 0 != x;
  {
  }

  lemma void after_part_chn_rec_no_effect(list<int> chns,
                                          int start, int len,
                                          int i)
  requires 0 <= start &*& 0 <= len &*& start + len <= i &*& i < length(chns);
  ensures nth(i, chns) == nth(i, add_partial_chain_rec_fp(chns, start, len));
  {
    switch(chns) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          if (len != 0) {
            assert 0 < i;
            gt_zero_neq_zero(i);
            assert 0 != i;
            after_part_chn_rec_no_effect(t, 0, len - 1, i - 1);
          }
        } else {
          assert 0 < i;
          after_part_chn_rec_no_effect(t, start - 1, len, i - 1);
        }
    }
  }

  lemma void before_part_chn_rec_no_effect(list<int> chns,
                                           int start, int len,
                                           int i)
  requires 0 <= start &*& 0 <= len &*& 0 <= i &*& i < start;
  ensures nth(i, chns) ==
          nth(i, add_partial_chain_rec_fp(chns, start, len));
  {
    switch(chns) {
      case nil:
      case cons(h,t):
          assert start != 0;
        if (i != 0) {
          before_part_chn_rec_no_effect(t, start - 1, len, i - 1);
        }
    }
  }
  @*/

/*@
  lemma void outside_part_chn_no_effect(list<int> chns, int start, int fin,
                                        int capacity)
  requires capacity == length(chns) &*& 0 <= fin &*& fin < capacity &*&
           0 <= start &*& start < capacity;
  ensures nth(fin, chns) ==
          nth(fin, add_partial_chain_fp(start, (fin < start) ?
                                                 capacity + fin - start :
                                                 fin - start,
                                        chns));
  {
    if (fin < start) {
      if (0 < fin) {
        before_part_chn_rec_no_effect(chns, start, capacity + fin - start, fin);
        add_part_chn_rec_same_len(start, capacity + fin - start, chns);
        after_part_chn_rec_no_effect
          (add_partial_chain_rec_fp(chns, start, capacity + fin - start),
                                     0, fin, fin);
      } else {
        assert fin == 0;
        before_part_chn_rec_no_effect(chns, start, capacity + fin - start, fin);
      }
    } else {
      after_part_chn_rec_no_effect(chns, start, fin - start, fin);
    }
  }//took 35m
  @*/

/*@
  lemma void add_part_chn_rec_add_one(list<int> chns, list<int> orig_chns,
                                      int start, int len)
  requires chns == add_partial_chain_rec_fp(orig_chns, start, len) &*&
           start + len + 1 <= length(orig_chns) &*&
           0 <= len &*&
           0 <= start;
  ensures update(start + len, nth(start + len, chns) + 1, chns) ==
          add_partial_chain_rec_fp(orig_chns, start, len + 1);
  {
    switch(orig_chns) {
      case nil:
      case cons(oh,ot):
        switch(chns) {
          case nil:
          case cons(rh,rt):
            if (start == 0) {
              if (len == 0) {
                add_part_chn_rec_zero_len(orig_chns, 0);
                add_part_chn_rec_zero_len(ot, 0);
              } else {
                add_part_chn_rec_add_one(rt, ot, 0, len - 1);
              }
            } else {
              add_part_chn_rec_add_one(rt, ot, start - 1, len);
            }
        }
    }
  }
  @*/

/*@
  lemma void two_inequalities_give_eq(int a, int b)
  requires a <= b &*& b <= a;
  ensures a == b;
  {
  }
  @*/

/*@
  lemma void add_part_chain_rec_overflow(list<int> chns,
                                         int start,
                                         int len1,
                                         int len2)
  requires length(chns) <= start + len1 &*&
           length(chns) <= start + len2;
  ensures add_partial_chain_rec_fp(chns, start, len1) ==
          add_partial_chain_rec_fp(chns, start, len2);
  {
    switch(chns) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          assert 0 < len1;
          assert 0 < len2;
          add_part_chain_rec_overflow(t, 0, len1 - 1, len2 - 1);
        } else {
          add_part_chain_rec_overflow(t, start - 1, len1, len2);
        }
    }
  }
  @*/

/*@
  lemma void Xchain_add_one(list<int> chns, list<int> orig_chns, int start,
                            int len, int capacity)
  requires chns == add_partial_chain_fp(start, len, orig_chns) &*&
           length(orig_chns) == capacity &*&
           0 <= start &*& start < capacity &*&
           0 <= len &*& len < capacity;
  ensures update(loop_fp(start + len, capacity),
                 nth(loop_fp(start + len, capacity), chns) + 1,
                 chns) ==
          add_partial_chain_fp(start, len+1, orig_chns);
  {
    if (length(orig_chns) < start + len) {
      add_part_chain_rec_overflow(orig_chns, start, len, len + 1);
      add_part_chn_rec_same_len(start, len, orig_chns);
      add_part_chn_rec_add_one(chns, add_partial_chain_rec_fp(orig_chns,
                                                              start, len),
                               0,
                               start + len - length(orig_chns));
      assert start + len - length(orig_chns) < capacity;
      loop_injection_n(start + len - length(orig_chns), capacity, 1);
      loop_bijection(start + len - length(orig_chns), capacity);
    } else {
      assert start + len <= capacity;
      if (start + len == capacity) {
        loop_injection_n(start + len - capacity, capacity, 1);
        loop_bijection(start + len - capacity, capacity);
        add_part_chain_rec_overflow(orig_chns, start, len, len + 1);
        add_part_chn_rec_zero_len
          (add_partial_chain_rec_fp(orig_chns, start, len+1), 0);
        add_part_chn_rec_same_len(start, len + 1, orig_chns);
        add_part_chn_rec_add_one(add_partial_chain_rec_fp
                                   (orig_chns, start, len+1),
                                 add_partial_chain_rec_fp
                                   (orig_chns, start, len+1),
                                 0, 0);
      } else {
        assert start + len < capacity;
       	add_part_chn_rec_add_one(chns, orig_chns, start, len);
       	loop_bijection(start + len, capacity);
      }
    }
  }//took 75m
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
  fixpoint list<bucket<kt> > empty_buckets_fp<kt>(nat len) {
    switch(len) {
      case zero: return nil;
      case succ(n):
        return cons(bucket(nil), empty_buckets_fp<kt>(n));
    }
  }
  @*/

/*@
  lemma void empty_buckets_empty_wraparound<kt>(nat capacity)
  requires true;
  ensures get_wraparound(nil, empty_buckets_fp<kt>(capacity)) == nil;
  {
    switch(capacity) {
      case zero:
      case succ(n):
        empty_buckets_empty_wraparound(n);
    }
  }
  @*/

/*@
  lemma void empty_buckets_chns_zeros_rec<kt>(nat capacity)
  requires true;
  ensures zero_list_fp(capacity) ==
          buckets_get_chns_rec_fp(nil, empty_buckets_fp<kt>(capacity));
  {
    switch(capacity) {
      case zero:
      case succ(n):
        empty_buckets_chns_zeros_rec(n);
    }
  }

  lemma void empty_buckets_chns_zeros<kt>(nat capacity)
  requires true;
  ensures zero_list_fp(capacity) ==
          buckets_get_chns_fp(empty_buckets_fp<kt>(capacity));
  {
    empty_buckets_empty_wraparound(capacity);
    empty_buckets_chns_zeros_rec(capacity);
  }
  @*/

/*@
  lemma void empty_buckets_ks_none_rec<kt>(nat capacity)
  requires true;
  ensures none_list_fp<kt>(capacity) ==
          buckets_get_keys_rec_fp(nil, empty_buckets_fp<kt>(capacity));
  {
    switch(capacity) {
      case zero:
      case succ(n):
        empty_buckets_ks_none_rec(n);
    }
  }

  lemma void empty_buckets_ks_none<kt>(nat capacity)
  requires capacity != zero;
  ensures none_list_fp<kt>(capacity) ==
          buckets_get_keys_fp(empty_buckets_fp<kt>(capacity));
  {
    empty_buckets_empty_wraparound(capacity);
    empty_buckets_ks_none_rec(capacity);
  }
  @*/

/*@
  lemma void empty_buckets_ok_rec<kt>(nat capacity, int bound)
  requires true;
  ensures true == buckets_ok_rec(nil, empty_buckets_fp<kt>(capacity), bound);
  {
    switch(capacity) {
      case zero:
      case succ(n):
        empty_buckets_ok_rec(n, bound);
    }
  }

  lemma void empty_buckets_length<kt>(nat len)
  requires true;
  ensures length(empty_buckets_fp<kt>(len)) == int_of_nat(len);
  {
    switch(len) {
      case zero:
      case succ(n):
        empty_buckets_length(n);
    }
  }

  lemma void empty_buckets_ok<kt>(nat capacity)
  requires capacity != zero;
  ensures true == buckets_ok(empty_buckets_fp<kt>(capacity));
  {
    empty_buckets_empty_wraparound(capacity);
    empty_buckets_length(capacity);
    empty_buckets_ok_rec(capacity, int_of_nat(capacity));
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

/*@
  lemma void buckets_put_same_len<kt>(list<bucket<kt> > buckets,
                                      kt k, int start, int dist)
  requires true;
  ensures length(buckets_put_key_fp(buckets, k, start, dist)) ==
          length(buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (start != 0)
          buckets_put_same_len(t, k, start - 1, dist);
    }
  }
  @*/


/*@
  lemma void advance_acc_still_eq<kt>(list<pair<kt, nat> > acc1,
                                      list<pair<kt, nat> > acc2)
  requires true == set_eq(acc1, acc2);
  ensures true == set_eq(advance_acc(acc1), advance_acc(acc2));
  {
    advance_acc_subset(acc1, acc2);
    advance_acc_subset(acc2, acc1);
  }

  lemma void acc_at_this_bucket_still_eq<kt>(list<pair<kt, nat> > acc1,
                                             list<pair<kt, nat> > acc2,
                                             bucket<kt> b)
  requires true == set_eq(acc1, acc2);
  ensures true == set_eq(acc_at_this_bucket(acc1, b),
                             acc_at_this_bucket(acc2, b));
  {
    acc_at_this_bucket_subset(acc1, acc2, b);
    acc_at_this_bucket_subset(acc2, acc1, b);
  }
  @*/

/*@
  fixpoint list<bucket<kt> > keep_short_fp<kt>(list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil:
        return nil;
      case cons(bh,bt):
        return switch(bh) { case bucket(chains):
          return cons(bucket(filter((upper_limit)(length(buckets)), chains)),
                      keep_short_fp(bt));
        };
    }
  }

  fixpoint bool lower_limit<kt>(int lim, pair<kt, nat> x) {
    switch(x) { case pair(key,dist):
      return lim <= int_of_nat(dist);
    }
  }

  fixpoint list<bucket<kt> > keep_long_fp<kt>(list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil:
        return nil;
      case cons(bh,bt):
        return switch(bh) { case bucket(chains):
          return cons(bucket(filter((lower_limit)(length(buckets)), chains)),
                      keep_long_fp(bt));
        };
    }
  }

  fixpoint bool buckets_short_fp<kt>(list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil: return true;
      case cons(bh,bt):
        return switch(bh) { case bucket(chains):
          return forall(chains, (upper_limit)(length(buckets))) &&
                 buckets_short_fp(bt);
        };
    }
  }

  fixpoint bool buckets_long_fp<kt>(list<bucket<kt> > buckets) {
    switch(buckets) {
      case nil: return true;
      case cons(bh,bt):
        return switch(bh) { case bucket(chains):
          return forall(chains, (lower_limit)(length(buckets))) &&
                 buckets_long_fp(bt);
        };
    }
  }

  fixpoint list<bucket<kt> > join_buckets_fp<kt>(list<bucket<kt> > bkts1,
                                                 list<bucket<kt> > bkts2) {
    switch(bkts1) {
      case nil:
        return nil; //bkts2 should be nil
      case cons(h1,t1):
        return switch(bkts2) {
          case nil:
            return nil; //must never happen
          case cons(h2,t2):
            return switch(h1) { case bucket(chains1):
              return switch(h2) { case bucket(chains2):
                return cons(bucket(append(chains1, chains2)),
                            join_buckets_fp(t1,t2));
              };
            };
        };
    }
  }

  fixpoint bool buckets_content_eq_fp<kt>(list<bucket<kt> > bkts1,
                                          list<bucket<kt> > bkts2) {
    switch(bkts1) {
      case nil:
        return bkts2 == nil;
      case cons(h1,t1):
        return switch(bkts2) {
          case nil: return false;
          case cons(h2,t2):
            return switch(h1) { case bucket(chains1):
              return switch(h2) { case bucket(chains2):
                return set_eq(chains1, chains2) &&
                       buckets_content_eq_fp(t1, t2);
              };
            };
        };
    }
  }

  @*/


/*@
  lemma void buckets_ok_short_long_ok_rec<kt>(list<pair<kt, nat> > acc1,
                                              list<pair<kt, nat> > acc2,
                                              list<pair<kt, nat> > acc,
                                              list<bucket<kt> > buckets,
                                              int bound)
  requires true == subset(acc1, acc) &*&
           true == subset(acc2, acc) &*&
           true == distinct(get_just_tails(acc1)) &*&
           true == distinct(get_just_tails(acc2)) &*&
           true == buckets_ok_rec(acc, buckets, bound);
  ensures true == buckets_ok_rec(acc1, keep_short_fp(buckets), bound) &*&
          true == buckets_ok_rec(acc2, keep_long_fp(buckets), bound);
  {
    switch(buckets) {
      case nil:
        subset_forall(acc1, acc, (upper_limit)(bound - 1));
        subset_forall(acc2, acc, (upper_limit)(bound - 1));
      case cons(h,t):
        list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb1 =
            append(acc1, filter((upper_limit)(length(buckets)), chains));
          list<pair<kt, nat> > atb2 =
            append(acc2, filter((lower_limit)(length(buckets)), chains));
          filter_subset((upper_limit)(length(buckets)), chains);
          filter_subset((lower_limit)(length(buckets)), chains);
          append_both_subset(acc1, chains, acc);
          assert true == subset(append(acc1, chains), atb);
          append_both_subset(filter((upper_limit)(length(buckets)), chains),
                             acc1,
                             chains);
          subset_trans(atb1, append(acc1, chains), atb);
          assert true == subset(atb1, append(acc1, chains));
          assert true == subset(atb1, atb);
          append_both_subset(acc2, chains, acc);
          append_both_subset(filter((lower_limit)(length(buckets)), chains),
                             acc2,
                             chains);
          subset_trans(atb2, append(acc2, chains), atb);
          assert true == subset(atb2, atb);
          map_append(snd, acc1, filter((upper_limit)(length(buckets)),
                                       chains));
          map_append(snd, acc2, filter((lower_limit)(length(buckets)),
                                       chains));
          map_append(snd, acc, filter((upper_limit)(length(buckets)),
                                      chains));
          map_append(snd, acc, filter((lower_limit)(length(buckets)),
                                      chains));
          map_append(snd, acc, chains);
          subset_map(acc1, acc, snd);
          subset_map(acc2, acc, snd);
          distinct_map_append_filter(snd,
                                     (upper_limit)(length(buckets)),
                                     acc, chains);
          distinct_map_append_filter(snd,
                                     (lower_limit)(length(buckets)),
                                     acc, chains);
          subset_append_distinct(get_just_tails(acc1),
                                 get_just_tails(acc),
                                 get_just_tails(filter((upper_limit)(length(buckets)),
                                                chains)));
          subset_append_distinct(get_just_tails(acc2),
                                 get_just_tails(acc),
                                 get_just_tails(filter((lower_limit)(length(buckets)),
                                                chains)));
          assert true == distinct(get_just_tails(atb1));
          assert true == distinct(get_just_tails(atb2));
          subset_forall(atb1, atb, (upper_limit)(bound));
          subset_forall(atb2, atb, (upper_limit)(bound));
          advance_acc_still_distinct(atb1);
          advance_acc_still_distinct(atb2);
          advance_acc_subset(atb1, atb);
          advance_acc_subset(atb2, atb);

          buckets_ok_short_long_ok_rec(advance_acc(atb1),
                                       advance_acc(atb2),
                                       advance_acc(atb),
                                       t, bound);
        }

    }
  }
  @*/


/*@
  lemma void buckets_ok_short_long_ok<kt>(list<pair<kt, nat> > acc,
                                          list<bucket<kt> > buckets,
                                          int bound)
  requires true == buckets_ok_rec(acc, buckets, bound);
  ensures true == buckets_ok_rec(acc,
                                 keep_short_fp(buckets),
                                 bound) &*&
          true == buckets_ok_rec(acc,
                                 keep_long_fp(buckets),
                                 bound);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          map_append(snd, acc, chains);
          distinct_unappend(get_just_tails(acc), get_just_tails(chains));
          assert true == distinct(get_just_tails(acc));
        }
    }
    buckets_ok_short_long_ok_rec(acc, acc, acc, buckets, bound);
  }//took 50m
  @*/


/*@
  lemma void advance_acc_cutoff_swap<kt>(list<pair<kt, nat> > acc, int cutoff)
  requires 0 < cutoff;
  ensures advance_acc(filter((upper_limit)(cutoff), acc)) ==
          filter((upper_limit)(cutoff-1), advance_acc(acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
          advance_acc_cutoff_swap(t, cutoff);
        }
    }
  }
  @*/


/*@
  lemma void filter_acc_cut_wraparound_same_keys<kt>(list<pair<kt, nat> > acc,
                                                     list<bucket<kt> > buckets)
  requires true;
  ensures buckets_get_keys_rec_fp(acc, buckets) ==
          buckets_get_keys_rec_fp(filter((upper_limit)(length(buckets)), acc),
                                  buckets);
  {
    assume(false);//TODO 15m
  }
  @*/

/*@
  lemma void keep_short_indeed_short<kt>(list<bucket<kt> > buckets)
  requires true;
  ensures true == buckets_short_fp(keep_short_fp(buckets));
  {
    assume(false);//TODO 5m
  }
  @*/

/*@
  lemma void keep_short_same_len<kt>(list<bucket<kt> > buckets)
  requires true;
  ensures length(buckets) == length(keep_short_fp(buckets));
  {
    assume(false);//TODO 5m
  }
  @*/

/*@
  lemma void keep_long_same_len<kt>(list<bucket<kt> > buckets)
  requires true;
  ensures length(buckets) == length(keep_long_fp(buckets));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains) :
          keep_long_same_len(t);
        }
    }
  }//took 2m
  @*/


/*@
  lemma void filter_long_chains_same_cur_key<kt>(list<pair<kt, nat> > acc,
                                                 int cutoff)
  requires 0 < cutoff;
  ensures get_current_key_fp(acc) ==
          get_current_key_fp(filter((upper_limit)(cutoff), acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
              filter_long_chains_same_cur_key(t, cutoff);
          }
        }
    }
  }
  @*/


/*@
  lemma void buckets_short_get_keys_rec<kt>(list<pair<kt, nat> > acc,
                                            list<bucket<kt> > buckets)
  requires true;
  ensures buckets_get_keys_rec_fp(acc, buckets) ==
          buckets_get_keys_rec_fp(acc, keep_short_fp(buckets));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > filter_acc =
           filter((upper_limit)(length(buckets)), acc);
        filter_acc_cut_wraparound_same_keys(acc, buckets);
        filter_acc_cut_wraparound_same_keys(acc, keep_short_fp(buckets));
        keep_short_same_len(buckets);
        filter_forall((upper_limit)(length(buckets)), acc);

        list<pair<kt, nat> > atb = acc_at_this_bucket(filter_acc, h);
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > short_atb =
            append(filter_acc, filter((upper_limit)(length(buckets)), chains));
          filter_append_idemp(filter_acc, chains, (upper_limit)(length(buckets)));
          filter_forall((upper_limit)(length(buckets)), filter_acc);
          assert short_atb == filter((upper_limit)(length(buckets)), atb);
          filter_long_chains_same_cur_key(atb, length(buckets));
          assert get_current_key_fp(atb) ==
                 get_current_key_fp(short_atb);
          filter_acc_cut_wraparound_same_keys(advance_acc(atb), t);
          advance_acc_cutoff_swap(atb, length(buckets));
          assert buckets_get_keys_rec_fp(advance_acc(atb), t) ==
                 buckets_get_keys_rec_fp(advance_acc(short_atb), t);
          buckets_short_get_keys_rec(advance_acc(short_atb), t);
        }
    }
  }//took 30m
  @*/

/*@
  lemma void buckets_put_key_keep_short_swap<kt>(list<bucket<kt> > buckets,
                                                 kt k, int start, int dist)
  requires start + dist < length(buckets);
  ensures keep_short_fp(buckets_put_key_fp(buckets, k, start, dist)) ==
          buckets_put_key_fp(keep_short_fp(buckets), k, start, dist);
  {
    assume(false);//TODO 10m
  }
  @*/

/*@
  lemma void buckets_put_key_keep_long_no_effect<kt>(list<bucket<kt> > buckets,
                                               kt k, int start, int dist)
  requires 0 <= start &*& start < length(buckets) &*&
           0 <= dist &*&
           start + dist < length(buckets);
  ensures keep_long_fp(buckets) ==
          keep_long_fp(buckets_put_key_fp(buckets, k, start, dist));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          if (start == 0) {
            assert dist < length(buckets);
            assert int_of_nat(nat_of_int(dist)) == dist;
            assert false == lower_limit(length(buckets), pair(k, nat_of_int(dist)));
            assert filter((lower_limit)(length(buckets)),
                          cons(pair(k, nat_of_int(dist)), chains)) ==
                   filter((lower_limit)(length(buckets)), chains);
          } else {
            buckets_put_same_len(buckets, k, start, dist);
            buckets_put_key_keep_long_no_effect(t, k, start - 1, dist);
          }
        }
    }
  
  }//took 30m
  @*/

/*@
  lemma void remove_advance_acc_swap<kt>(list<pair<kt, nat> > acc, kt k, nat n)
  requires true;
  ensures remove(pair(k, n), advance_acc(acc)) ==
          advance_acc(remove(pair(k, succ(n)), acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(x):
          }
        }
        if (h != pair(k, succ(n))) remove_advance_acc_swap(t, k, n);
    }
  }
  @*/


/*@
  lemma void advance_acc_removes_zero<kt>(list<pair<kt, nat> > acc, kt k)
  requires true;
  ensures advance_acc(remove(pair(k, zero), acc)) == advance_acc(acc);
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(x):
          }
        }
      if (h != pair(k, zero)) advance_acc_removes_zero(t, k);
    }
  }
  @*/



/*@
  lemma void advance_acc_multiset_eq<kt>(list<pair<kt, nat> > acc1,
                                         list<pair<kt, nat> > acc2)
  requires true == multiset_eq(acc1, acc2);
  ensures true == multiset_eq(advance_acc(acc1), advance_acc(acc2));
  {
    switch(acc1) {
      case nil:
      case cons(h,t):
        advance_acc_multiset_eq(t, remove(h, acc2));
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
              advance_acc_removes_zero(acc2, key);
            case succ(n):
              mem_advance_acc_swap(acc2, key, n);
              remove_advance_acc_swap(acc2, key, n);
          }
        }
    }
  }
  @*/

/*@
  lemma void distinct_and_disjoint_append<t>(list<t> l1, list<t> l2)
  requires true == distinct(l1) &*&
           true == distinct(l2) &*&
           intersection(l1, l2) == nil;
  ensures true == distinct(append(l1,l2));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void multiset_eq_map<t1,t2>(fixpoint (t1,t2) f,
                                    list<t1> l1,
                                    list<t1> l2)
  requires true == multiset_eq(l1, l2);
  ensures true == multiset_eq(map(f, l1), map(f, l2));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void multiset_eq_distinct<t>(list<t> l1, list<t> l2)
  requires true == multiset_eq(l1, l2);
  ensures distinct(l1) == distinct(l2);
  {
    assume(false);//TODO 
  }
  @*/

/*@
  lemma void multiset_eq_forall<t>(list<t> l1, list<t> l2, fixpoint (t,bool) f)
  requires true == multiset_eq(l1, l2);
  ensures forall(l1, f) == forall(l2, f);
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void multiset_eq_append_assoc<t>(list<t> l1, list<t> l2, list<t> l3)
  requires true;
  ensures true == multiset_eq(append(append(l1, l2), l3),
                              append(l1, append(l2, l3)));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void multiset_eq_append<t>(list<t> l1, list<t> l2,
                                   list<t> l3, list<t> l4)
  requires true == multiset_eq(l1, l2) &*&
           true == multiset_eq(l3, l4);
  ensures true == multiset_eq(append(l1, l3), append(l2, l4));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void multiset_eq_append_comm<t>(list<t> l1, list<t> l2)
  requires true;
  ensures true == multiset_eq(append(l1, l2), append(l2, l1));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void multiset_eq_trans<t>(list<t> l1, list<t> l2, list<t> l3)
  requires true == multiset_eq(l1, l2) &*&
           true == multiset_eq(l2, l3);
  ensures true == multiset_eq(l1, l3);
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void eq_multiset_eq<t>(list<t> l1, list<t> l2)
  requires l1 == l2;
  ensures true == multiset_eq(l1, l2);
  {
    multiset_eq_refl(l1);
  }
  @*/


/*@
  lemma void intersection_nil_comm<t>(list<t> l1, list<t> l2)
  requires true;
  ensures true == ((intersection(l1, l2) == nil) ==
                   (intersection(l2, l1) == nil));
  {
    assume(false);//TODO 
  }
  @*/

/*@
  lemma void intersection_nil_append<t>(list<t> l1, list<t> l2,
                                        list<t> l3, list<t> l4)
  requires intersection(l1, l3) == nil &*&
           intersection(l2, l4) == nil;
  ensures intersection(append(l1, l2), append(l3, l4)) == nil;
  {
    assume(false);//TODO 
  }
  @*/

/*@
  lemma void advance_acc_still_disjoint<kt>(list<pair<kt, nat> > acc1,
                                            list<pair<kt, nat> > acc2)
  requires intersection(get_just_tails(acc1),
                        get_just_tails(acc2)) == nil;
  ensures intersection(get_just_tails(advance_acc(acc1)),
                       get_just_tails(advance_acc(acc2))) == nil;
  {
    switch(acc2) {
      case nil:
      case cons(h,t):
        advance_acc_still_disjoint(acc1, t);
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
              advance_acc_dec_nonmem(n, acc1);
          }
        }
    }
  }//took 7m
  @*/


/*@
  fixpoint bool ge_than(int lim, nat x) {return lim <= int_of_nat(x); }

  lemma void lower_limit_ge_than<kt>(list<pair<kt, nat> > l, int lim)
  requires true;
  ensures true == forall(get_just_tails(filter((lower_limit)(lim), l)),
                         (ge_than)(lim));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist): }
        lower_limit_ge_than(t, lim);
    }
  }
  @*/

/*@
  lemma void upper_limit_less_than<kt>(list<pair<kt, nat> > l, int lim)
  requires true;
  ensures true == forall(get_just_tails(filter((upper_limit)(lim), l)),
                         (less_than)(lim));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist): }
        upper_limit_less_than(t, lim);
    }
  
  }
  @*/


/*@
  lemma void less_than_and_ge_disjoint(list<nat> lst, int lim)
  requires true == forall(lst, (less_than)(lim)) &*&
           true == forall(lst, (ge_than)(lim));
  ensures lst == nil;
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        assert true == less_than(lim, h);
        assert true == ge_than(lim, h);
    }
  }
  @*/


/*@
  lemma void intersection_subset<t>(list<t> l1, list<t> l2)
  requires true;
  ensures true == subset(intersection(l1, l2), l1) &*&
          true == subset(intersection(l1, l2), l2);
  {
    switch(l2) {
      case nil:
      case cons(h,t):
        intersection_subset(l1, t);
        if (contains(l1, h)) {
          subset_unremove(intersection(l1, l2), t, h);
        } else {
          add_extra_preserves_subset(intersection(l1, l2), t, h);
        }
    }
  }//took 27m
  @*/


/*@
  lemma void lower_and_upper_limit_complement<kt>(list<pair<kt, nat> > l,
                                                  int lim)
  requires true;
  ensures true == multiset_eq(append(filter((lower_limit)(lim), l),
                                     filter((upper_limit)(lim), l)), l) &*&
          intersection(get_just_tails(filter((lower_limit)(lim), l)),
                       get_just_tails(filter((upper_limit)(lim), l))) == nil;
  {
    switch(l) {
      case nil:
      case cons(h,t):
        lower_and_upper_limit_complement(t, lim);
        switch(h) { case pair(key, dist): }
        if (lower_limit(lim, h)) {
        } else {
          assert true == upper_limit(lim, h);
          cons_in_the_middle_multiset_eq
          (filter((lower_limit)(lim), t), filter((upper_limit)(lim), t), h);
          multiset_eq_trans(append(filter((lower_limit)(lim), l),
                                   filter((upper_limit)(lim), l)),
                            cons(h, append(filter((lower_limit)(lim), t),
                                           filter((upper_limit)(lim), t))),
                            l);
        }
        upper_limit_less_than(l, lim);
        lower_limit_ge_than(l, lim);
        intersection_subset(get_just_tails(filter((lower_limit)(lim), l)),
                            get_just_tails(filter((upper_limit)(lim), l)));
        list<nat> inters =
          intersection(get_just_tails(filter((lower_limit)(lim), l)),
                      get_just_tails(filter((upper_limit)(lim), l)));
        subset_forall(inters, get_just_tails(filter((lower_limit)(lim), l)),
                      (ge_than)(lim));
        subset_forall(inters, get_just_tails(filter((upper_limit)(lim), l)),
                      (less_than)(lim));
        less_than_and_ge_disjoint(inters, lim);
    }
  }//took 55m
  @*/

/*@
  lemma void multiset_eq_reshuffle_appends<t>(list<t> l1, list<t> l2,
                                              list<t> l3, list<t> l4,
                                              list<t> l5)
  requires true == multiset_eq(l1, append(append(l2, l3), append(l4, l5)));
  ensures true == multiset_eq(l1, append(append(l2, l5), append(l3, l4)));
  {
    multiset_eq_append_assoc(l2, l3, append(l4, l5));
    multiset_eq_trans(l1, append(append(l2, l3),
                                  append(l4, l5)),
                      append(l2, append(l3, append(l4, l5))));
    assert true == multiset_eq(l1, append(l2, append(l3, append(l4, l5))));
    multiset_eq_append_assoc(l3, l4, l5);
    multiset_eq_comm(append(append(l3, l4), l5),
                      append(l3, append(l4, l5)));
    multiset_eq_append_comm(append(l3, l4), l5);
    multiset_eq_trans(append(l3, append(l4, l5)),
                      append(append(l3, l4), l5),
                      append(l5, append(l3, l4)));
    multiset_eq_refl(l2);
    multiset_eq_append(l2, l2,
                        append(l3, append(l4, l5)),
                        append(l5, append(l3, l4)));
    multiset_eq_trans(l1,
                      append(l2, append(l3, append(l4, l5))),
                      append(l2, append(l5, append(l3, l4))));
    assert true == multiset_eq(l1, append(l2, append(l5, append(l3, l4))));
    multiset_eq_append_assoc(l2, l5, append(l3, l4));
    multiset_eq_comm(append(append(l2, l5), append(l3, l4)),
                      append(l2, append(l5, append(l3, l4))));
    assert true == multiset_eq(append(l2, append(l5, append(l3, l4))),
                                append(append(l2, l5), append(l3, l4)));
    assert true == multiset_eq(append(l2, append(l5, append(l3, l4))),
                                append(append(l2, l5), append(l3, l4)));

    multiset_eq_trans(l1, append(l2, append(l5, append(l3, l4))),
                      append(append(l2, l5), append(l3, l4)));
  }
  @*/


/*@
  lemma void buckets_split_ok_orig_ok_rec<kt>(list<pair<kt, nat> > sacc,
                                              list<pair<kt, nat> > lacc,
                                              list<pair<kt, nat> > acc,
                                              list<bucket<kt> > buckets,
                                              int bound)
  requires true == buckets_ok_rec(sacc, keep_short_fp(buckets), bound) &*&
           true == buckets_ok_rec(lacc, keep_long_fp(buckets), bound) &*&
           intersection(get_just_tails(sacc), get_just_tails(lacc)) == nil &*&
           true == multiset_eq(acc, append(sacc, lacc));
  ensures true == buckets_ok_rec(acc, buckets, bound);
  {
    switch(buckets) {
      case nil:
        map_append(snd, sacc, lacc);
        distinct_and_disjoint_append(get_just_tails(sacc), get_just_tails(lacc));
        multiset_eq_map(snd, acc, append(sacc, lacc));
        multiset_eq_distinct(get_just_tails(acc),
                             get_just_tails(append(sacc, lacc)));
        forall_append(sacc, lacc, (upper_limit)(bound - 1));
        multiset_eq_forall(acc, append(sacc, lacc), (upper_limit)(bound - 1));
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > lchains =
            filter((lower_limit)(length(buckets)), chains);
          list<pair<kt, nat> > schains =
            filter((upper_limit)(length(buckets)), chains);
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > satb = append(sacc, schains);
          list<pair<kt, nat> > latb = append(lacc, lchains);

          lower_and_upper_limit_complement(chains, length(buckets));
          multiset_eq_comm(append(lchains, schains), chains);
          map_append(snd, acc, chains);
          map_append(snd, sacc, schains);
          map_append(snd, lacc, lchains);
          assert true == multiset_eq(acc, append(sacc, lacc));
          assert true == multiset_eq(chains, append(lchains, schains));
          assert atb == append(acc, chains);
          eq_multiset_eq(atb, append(acc, chains));
          multiset_eq_append(acc, append(sacc, lacc),
                             chains, append(lchains, schains));
          multiset_eq_trans(atb, append(acc, chains),
                            append(append(sacc, lacc), append(lchains, schains)));


          assert true == multiset_eq(atb, append(append(sacc, lacc), append(lchains, schains)));
          multiset_eq_reshuffle_appends(atb, sacc, lacc, lchains, schains);
          assert true == multiset_eq(atb, append(append(sacc, schains), append(lacc, lchains)));
          assert true == multiset_eq(atb, append(satb, latb));
          assert true == distinct(get_just_tails(satb));
          assert true == distinct(get_just_tails(latb));
          assert intersection(get_just_tails(sacc),
                              get_just_tails(lacc)) == nil;
          intersection_nil_comm(get_just_tails(lchains),
                            get_just_tails(schains));
          assert intersection(get_just_tails(schains),
                              get_just_tails(lchains)) == nil;
          intersection_nil_append(get_just_tails(sacc), get_just_tails(schains),
                                  get_just_tails(lacc), get_just_tails(lchains));
          assert intersection(get_just_tails(satb),
                              get_just_tails(latb)) == nil;
          distinct_and_disjoint_append(get_just_tails(satb),
                                       get_just_tails(latb));
          map_append(snd, satb, latb);
          assert true == distinct(get_just_tails(append(satb, latb)));
          multiset_eq_map(snd, atb, append(satb, latb));
          multiset_eq_distinct(get_just_tails(atb),
                               get_just_tails(append(satb, latb)));
          assert true == distinct(get_just_tails(atb));
          advance_acc_still_distinct(atb);
          assert true == forall(satb, (upper_limit)(bound));
          assert true == forall(latb, (upper_limit)(bound));
          forall_append(satb, latb, (upper_limit)(bound));
          assert true == forall(append(satb, latb), (upper_limit)(bound));
          multiset_eq_forall(atb, append(satb, latb), (upper_limit)(bound));
          assert true == forall(atb, (upper_limit)(bound));
          assert true == multiset_eq(atb, append(satb, latb));
          advance_acc_multiset_eq(atb, append(satb, latb));
          advance_acc_append_commute(satb, latb);
          advance_acc_still_disjoint(satb, latb);
          buckets_split_ok_orig_ok_rec(advance_acc(satb),
                                       advance_acc(latb),
                                       advance_acc(atb),
                                       t,
                                       bound);
        }
    }
  }
  @*/

/*@
  fixpoint bool msubset<t>(list<t> l1, list<t> l2) {
    switch(l1) {
      case nil: return true;
      case cons(h,t):
        return true == mem(h, l2) && msubset(t, remove(h, l2));
    }
  }
  @*/


/*@
  lemma void filter_msubset<t>(fixpoint (t, bool) f, list<t> l)
  requires true;
  ensures true == msubset(filter(f, l), l);
  {
    assume(false);//TODO
  }
  @*/


/*@
  lemma void msubset_distinct<t>(list<t> l1, list<t> l2)
  requires true == msubset(l1, l2) &*& true == distinct(l2);
  ensures true == distinct(l1);
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void msubset_subset<t>(list<t> l1, list<t> l2)
  requires true == msubset(l1, l2);
  ensures true == subset(l1, l2);
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void msubset_map<t1, t2>(fixpoint (t1, t2) f, list<t1> l1, list<t1> l2)
  requires true == msubset(l1, l2);
  ensures true == msubset(map(f, l1), map(f, l2));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void buckets_split_ok_orig_ok<kt>(list<pair<kt, nat> > acc,
                                          list<bucket<kt> > buckets,
                                          int bound)
  requires true == buckets_ok_rec(acc, keep_short_fp(buckets), bound) &*&
           true == buckets_ok_rec(acc, keep_long_fp(buckets), bound);
  ensures true == buckets_ok_rec(acc, buckets, bound);
  {
    list<pair<kt, nat> > sacc = filter((upper_limit)(length(buckets)), acc);
    list<pair<kt, nat> > lacc = filter((lower_limit)(length(buckets)), acc);
    filter_msubset((upper_limit)(length(buckets)), acc);
    filter_msubset((lower_limit)(length(buckets)), acc);
    msubset_subset(sacc, acc);
    msubset_subset(lacc, acc);
    msubset_map(snd, sacc, acc);
    msubset_map(snd, lacc, acc);
    buckets_ok_rec_acc_tails_distinct(acc, keep_short_fp(buckets), bound);
    msubset_distinct(get_just_tails(sacc), get_just_tails(acc));
    msubset_distinct(get_just_tails(lacc), get_just_tails(acc));
    lower_and_upper_limit_complement(acc, length(buckets));
    acc_subset_buckets_still_ok_rec(sacc, acc, keep_short_fp(buckets), bound);
    acc_subset_buckets_still_ok_rec(lacc, acc, keep_long_fp(buckets), bound);
    intersection_nil_comm(get_just_tails(sacc), get_just_tails(lacc));
    multiset_eq_append_comm(sacc, lacc);
    multiset_eq_trans(append(sacc, lacc), append(lacc, sacc), acc);
    multiset_eq_comm(append(sacc, lacc), acc);
    buckets_split_ok_orig_ok_rec(sacc, lacc, acc,
                                 buckets, bound);
  }//took 40m
  @*/


/*@
  lemma void distinct_unmap<t1,t2>(list<t1> lst, fixpoint (t1,t2) f)
  requires true == distinct(map(f, lst));
  ensures true == distinct(lst);
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        if (mem(h, t)) {
          mem_map(h, t, f);
          assert true == mem(f(h), map(f, t));
        }
        distinct_unmap(t, f);
    }
  }
  @*/

/*@
  lemma void accs_eq_tails_distinct<kt>(list<pair<kt, nat> > acc1,
                                        list<pair<kt, nat> > acc2)
  requires true == distinct(get_just_tails(acc1)) &*&
           true == set_eq(acc1, acc2) &*&
           length(acc1) == length(acc2);
  ensures true == distinct(get_just_tails(acc2));
  {
    content_eq_map(acc1, acc2, snd);
    map_preserves_length(snd, acc1);
    map_preserves_length(snd, acc2);
    set_eq_same_len_distinct_both(get_just_tails(acc1),
                                  get_just_tails(acc2));
  }

  @*/

/*@
  lemma void acc_eq_buckets_ok_rec<kt>(list<pair<kt, nat> > acc1,
                                       list<pair<kt, nat> > acc2,
                                       list<bucket<kt> > buckets,
                                       int bound)
  requires true == set_eq(acc1, acc2) &*&
           true == buckets_ok_rec(acc1, buckets, bound) &*&
           true == distinct(get_just_tails(acc2));
  ensures true == buckets_ok_rec(acc2, buckets, bound);
  {
    switch(buckets) {
      case nil:
        set_eq_forall_both(acc1, acc2, (upper_limit)(bound - 1));
      case cons(h,t):
        list<pair<kt, nat> > atb1 = acc_at_this_bucket(acc1, h);
        list<pair<kt, nat> > atb2 = acc_at_this_bucket(acc2, h);
        switch(h) { case bucket(chains):
          map_append(snd, acc1, chains);
          distinct_unappend(get_just_tails(acc1), get_just_tails(chains));
        }
        distinct_unmap(acc1, snd);
        distinct_unmap(acc2, snd);
        set_eq_distinct_same_len(acc1, acc2);
        assert length(atb1) == length(atb2);
        acc_at_this_bucket_still_eq(acc1, acc2, h);
        accs_eq_tails_distinct(atb1, atb2);
        set_eq_forall_both(atb1, atb2, (upper_limit)(bound));
        advance_acc_still_eq(atb1, atb2);
        advance_acc_still_distinct(atb2);
        acc_eq_buckets_ok_rec(advance_acc(atb1), advance_acc(atb2), t, bound);
    }
  }//took 60m
  @*/

/*@
  lemma void acc_at_bucket_put_is_cons<kt>(list<pair<kt, nat> > acc,
                                           bucket<kt> bucket,
                                           kt k, int dist)
  requires true;
  ensures true == set_eq
                    (acc_at_this_bucket(acc, bucket_put_key_fp(bucket, k, dist)),
                     cons(pair(k, nat_of_int(dist)),
                          acc_at_this_bucket(acc, bucket))) &*&
          length(acc_at_this_bucket(acc, bucket_put_key_fp(bucket, k, dist))) ==
          length(acc_at_this_bucket(acc, bucket)) + 1;
  {
    switch(bucket) { case bucket(chains):
      list<pair<kt, nat> > atb = acc_at_this_bucket(acc, bucket);
      list<pair<kt, nat> > atb_add =
        acc_at_this_bucket(acc, bucket_put_key_fp(bucket, k, dist));
      cons_in_the_middle_multiset_eq(acc, chains, pair(k, nat_of_int(dist)));
      multiset_eq_set_eq(atb_add, cons(pair(k, nat_of_int(dist)), atb));
      multiset_eq_same_len(atb_add, cons(pair(k, nat_of_int(dist)), atb));
    }
  }//took 5m (again, kind of a duplicate of another lemma)
  @*/


/*@
  lemma void acc_eq_get_chns_eq<kt>(list<pair<kt, nat> > acc1,
                                    list<pair<kt, nat> > acc2,
                                    list<bucket<kt> > buckets)
  requires true == multiset_eq(acc1, acc2);
  ensures buckets_get_chns_rec_fp(acc1, buckets) ==
          buckets_get_chns_rec_fp(acc2, buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb1 = acc_at_this_bucket(acc1, h);
          list<pair<kt, nat> > atb2 = acc_at_this_bucket(acc2, h);
          multiset_eq_append_both(acc1, acc2, chains);
          advance_acc_multiset_eq(atb1, atb2);
          multiset_eq_same_len(advance_acc(atb1), advance_acc(atb2));
          acc_eq_get_chns_eq(advance_acc(atb1), advance_acc(atb2), t);
        }
    }
  }
  @*/


/*@
  lemma void
  acc_eq_cons_get_chns_like_add_part_chn<kt>(list<pair<kt, nat> > acc,
                                             list<pair<kt, nat> > orig,
                                             list<bucket<kt> > buckets,
                                             kt k, int dist)
  requires 0 <= dist &*&
           true == multiset_eq(acc, cons(pair(k, nat_of_int(dist)), orig));
  ensures buckets_get_chns_rec_fp(acc, buckets) ==
          add_partial_chain_rec_fp(buckets_get_chns_rec_fp(orig, buckets),
                                   0, dist);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
        list<pair<kt, nat> > orig_atb = acc_at_this_bucket(orig, h);
        switch(h) { case bucket(chains):
          multiset_eq_append_both(acc, cons(pair(k, nat_of_int(dist)), orig),
                                  chains);
          assert true == multiset_eq(atb, cons(pair(k, nat_of_int(dist)),
                                               orig_atb));
          advance_acc_multiset_eq(atb, cons(pair(k, nat_of_int(dist)),
                                            orig_atb));
          multiset_eq_same_len(advance_acc(atb),
                               advance_acc(cons(pair(k, nat_of_int(dist)),
                                                orig_atb)));
          if (dist == 0) {
            assert advance_acc(cons(pair(k, nat_of_int(dist)), orig_atb)) ==
                   advance_acc(orig_atb);
            assert true == multiset_eq(advance_acc(atb), advance_acc(orig_atb));
            acc_eq_get_chns_eq(advance_acc(atb), advance_acc(orig_atb), t);
          } else {
            nat prev_d = nat_of_int(dist - 1);
            assert nat_of_int(dist) == succ(prev_d);
            acc_eq_cons_get_chns_like_add_part_chn(advance_acc(atb),
                                                   advance_acc(orig_atb),
                                                   t, k, dist - 1);
          }
        }
    }
  }
  @*/

/*@
  lemma void acc_additional_zero_chain_same_chns<kt>(list<pair<kt, nat> > acc1,
                                                     list<pair<kt, nat> > acc2,
                                                     list<bucket<kt> > buckets,
                                                     kt k)
  requires true == multiset_eq(acc1, cons(pair(k, zero), acc2)) &*&
           buckets != nil;
  ensures buckets_get_chns_rec_fp(acc1, buckets) ==
          buckets_get_chns_rec_fp(acc2, buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
    }
    assert 0 < length(buckets);
    acc_eq_cons_get_chns_like_add_part_chn(acc1, acc2, buckets, k, 0);
    add_part_chn_zero_len(buckets_get_chns_rec_fp(acc2, buckets), 0);
  }
  @*/

/*@
  lemma void long_chain_in_acc_to_wraparound<kt>(list<pair<kt, nat> > acc,
                                                 list<pair<kt, nat> > orig,
                                                 list<bucket<kt> > buckets,
                                                 kt k, int dist)
  requires true == multiset_eq(acc, cons(pair(k, nat_of_int(dist)), orig)) &*&
           length(buckets) <= dist;
  ensures true == multiset_eq(get_wraparound(acc, buckets),
                              cons(pair(k, nat_of_int(dist - length(buckets))),
                                   get_wraparound(orig, buckets)));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > orig_atb = acc_at_this_bucket(orig, h);
          multiset_eq_append_both(acc, cons(pair(k, nat_of_int(dist)), orig),
                                  chains);
          assert 0 < dist;
          int prev_dist = dist - 1;
          assert nat_of_int(dist) == succ(nat_of_int(prev_dist));
          advance_acc_multiset_eq(atb, cons(pair(k, nat_of_int(dist)),
                                            orig_atb));
          long_chain_in_acc_to_wraparound(advance_acc(atb), advance_acc(orig_atb),
                                          t, k, dist - 1);
        }
    }
  }
  @*/

/*@
  lemma void buckets_put_wraparound_eq_cons<kt>(list<pair<kt, nat> > acc,
                                                list<bucket<kt> > buckets,
                                                kt k, int start, int dist)
  requires length(buckets) <= start + dist &*&
           0 <= start &*& start < length(buckets);
  ensures true == multiset_eq(get_wraparound(acc, buckets_put_key_fp
                                                    (buckets, k, start, dist)),
                              cons(pair(k, nat_of_int(dist + start -
                                                      length(buckets))),
                                   get_wraparound(acc, buckets)));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          if (start == 0) {
            list<pair<kt, nat> > new_atb =
              acc_at_this_bucket(acc, bucket_put_key_fp(h, k, dist));
            cons_in_the_middle_multiset_eq(acc, chains,
                                           pair(k, nat_of_int(dist)));
            assert true == multiset_eq
                             (new_atb, cons(pair(k, nat_of_int(dist)), atb));
            advance_acc_multiset_eq(new_atb, cons(pair(k, nat_of_int(dist)),
                                                  atb));
            assert 0 < dist;
            int prev_dist = dist - 1;
            assert nat_of_int(dist) == succ(nat_of_int(prev_dist));
            long_chain_in_acc_to_wraparound
              (advance_acc(new_atb), advance_acc(atb), t, k, prev_dist);
          } else {
            buckets_put_wraparound_eq_cons
              (advance_acc(atb), t, k, start - 1, dist);
          }
        }
    }
  }
  @*/
/*@
  lemma void buckets_put_wraparound_is_cons<kt>(list<pair<kt, nat> > acc,
                                                list<bucket<kt> > buckets,
                                                kt k, int start, int dist)
  requires length(buckets) <= dist + start &*&
           0 <= start &*& start < length(buckets);
  ensures true == set_eq
                    (get_wraparound(acc,
                                    buckets_put_key_fp(buckets, k,
                                                       start, dist)),
                     cons(pair(k, nat_of_int(dist + start - length(buckets))),
                          get_wraparound(acc, buckets))) &*&
          length(get_wraparound(acc, buckets_put_key_fp(buckets, k,
                                                        start, dist))) ==
          length(get_wraparound(acc, buckets)) + 1;
  {
    buckets_put_wraparound_eq_cons(acc, buckets, k, start, dist);
    list<pair<kt, nat> > wrp1 = get_wraparound(acc,
                                               buckets_put_key_fp(buckets, k,
                                                                  start, dist));
    list<pair<kt, nat> > wrp2 =
      cons(pair(k, nat_of_int(dist + start - length(buckets))),
           get_wraparound(acc, buckets));

    multiset_eq_set_eq(wrp1, wrp2);
    multiset_eq_same_len(wrp1, wrp2);
  }//took 10m (it is kind of a duplicate of another, more strong lemma)
  @*/


/*@
  lemma void get_current_key_none_subset_none<kt>(list<pair<kt, nat> > acc1,
                                                  list<pair<kt, nat> > acc2)
  requires get_current_key_fp(acc1) == none &*&
           true == subset(acc2, acc1);
  ensures get_current_key_fp(acc2) == none;
  {
    switch(acc2) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
              subset_mem_trans(acc2, acc1, h);
              assert true == mem(h, acc1);
              mem_map(h, acc1, snd);
              assert true == mem(zero, get_just_tails(acc1));
              nozero_no_current_key(acc1);
              assert false;
            case succ(n):
              get_current_key_none_subset_none(acc1, t);
          }
        }
    }
  }//took 8m
  @*/


/*@
  lemma void acc_subset_also_none<kt>(list<pair<kt, nat> > acc1,
                                      list<pair<kt, nat> > acc2,
                                      list<bucket<kt> > buckets,
                                      int x)
  requires 0 <= x &*& x < length(buckets) &*&
           nth(x, buckets_get_keys_rec_fp(acc1, buckets)) == none &*&
           true == subset(acc2, acc1);
  ensures nth(x, buckets_get_keys_rec_fp(acc2, buckets)) == none;
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb1 = acc_at_this_bucket(acc1, h);
          list<pair<kt, nat> > atb2 = acc_at_this_bucket(acc2, h);
          append_both_subset(acc2, chains, acc1);
          if (x == 0) {
            get_current_key_none_subset_none(atb1, atb2);
          } else {
            advance_acc_subset(atb2, atb1);
            acc_subset_also_none(advance_acc(atb1), advance_acc(atb2),
                                 t, x - 1);
          }
        }
    }
  }//took 5m
  @*/


/*@
  lemma void no_key_especially_in_short_and_long<kt>(list<pair<kt, nat> > acc,
                                                     list<bucket<kt> > buckets,
                                                     int x)
  requires 0 <= x &*& x < length(buckets) &*&
           nth(x, buckets_get_keys_rec_fp(acc, buckets)) == none;
  ensures nth(x, buckets_get_keys_rec_fp(acc, keep_long_fp(buckets))) == none &*&
          nth(x, buckets_get_keys_rec_fp(acc, keep_short_fp(buckets))) == none;
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > latb =
            append(acc, filter((lower_limit)(length(buckets)), chains));
          list<pair<kt, nat> > satb =
            append(acc, filter((upper_limit)(length(buckets)), chains));
          filter_subset((lower_limit)(length(buckets)), chains);
          filter_subset((upper_limit)(length(buckets)), chains);
          append_both_subset(filter((lower_limit)(length(buckets)), chains),
                             acc,
                             chains);
          append_both_subset(filter((upper_limit)(length(buckets)), chains),
                             acc,
                             chains);
          assert true == subset(latb, atb);
          assert true == subset(satb, atb);
          if (x == 0) {
            get_current_key_none_subset_none(atb, latb);
            get_current_key_none_subset_none(atb, satb);
          } else {
            advance_acc_subset(latb, atb);
            advance_acc_subset(satb, atb);
            no_key_especially_in_short_and_long(advance_acc(atb), t, x - 1);
            keep_long_same_len(t);
            keep_short_same_len(t);
            acc_subset_also_none(advance_acc(atb), advance_acc(latb),
                                 keep_long_fp(t), x - 1);
            acc_subset_also_none(advance_acc(atb), advance_acc(satb),
                                 keep_short_fp(t), x - 1);
          }
        }
    }
  }//took 30m
  @*/

/*@
  lemma void advance_acc_keeps_tail_mem<kt>(list<pair<kt, nat> > acc,
                                            nat dist)
  requires true;
  ensures mem(dist, get_just_tails(advance_acc(acc))) ==
          mem(succ(dist), get_just_tails(acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,d):
          switch(d) {
            case zero:
            case succ(n):
          }
        }
        advance_acc_keeps_tail_mem(t, dist);
    }
  
  }//took 5m
  @*/

/*@
  lemma void get_key_none_no_chain<kt>(list<pair<kt, nat> > acc,
                                       list<bucket<kt> > buckets,
                                       int dist)
  requires 0 <= dist &*& dist < length(buckets) &*&
           nth(dist, buckets_get_keys_rec_fp(acc, buckets)) == none;
  ensures false == mem(nat_of_int(dist), get_just_tails(acc));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
        if (dist == 0) {
          if (mem(zero, get_just_tails(atb))) {
            nozero_no_current_key(atb);
          }
        } else {
          get_key_none_no_chain(advance_acc(atb), t, dist - 1);
          assert succ(nat_of_int(dist - 1)) == nat_of_int(dist);
          advance_acc_keeps_tail_mem(atb, nat_of_int(dist - 1));
          assert false == mem(nat_of_int(dist), get_just_tails(atb));
        }
        switch(h) { case bucket(chains):
          map_append(snd, acc, chains);
          assert false == mem(nat_of_int(dist), get_just_tails(acc));
        }
    }
  }//took 15m
  @*/

/*@
  lemma void cons_acc_atb_swap<kt>(list<pair<kt, nat> > acc,
                                   bucket<kt> b,
                                   pair<kt, nat> x)
  requires true;
  ensures acc_at_this_bucket(cons(x, acc), b) ==
          cons(x, acc_at_this_bucket(acc, b));
  {
    switch(b) { case bucket(chains):
    }
  }//took 2m
  @*/

/*@
  lemma void
  acc_add_chain_buckets_ok_rec<kt>(list<pair<kt, nat> > acc,
                                   list<bucket<kt> > buckets,
                                   kt k, int dist,
                                   int bound)
  requires 0 <= dist &*& dist < length(buckets) &*&
           length(buckets) <= bound &*&
           nth(dist, buckets_get_keys_rec_fp(acc, buckets)) == none &*&
           true == buckets_ok_rec(acc, buckets, bound);
  ensures true == buckets_ok_rec(cons(pair(k, nat_of_int(dist)), acc),
                                 buckets, bound);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
        list<pair<kt, nat> > new_acc_atb =
          acc_at_this_bucket(cons(pair(k, nat_of_int(dist)), acc), h);
        cons_acc_atb_swap(acc, h, pair(k, nat_of_int(dist)));
        assert new_acc_atb == cons(pair(k, nat_of_int(dist)), acc_atb);
        assert true == forall(new_acc_atb, (upper_limit)(bound));
        if (dist == 0) {
          assert advance_acc(acc_atb) == advance_acc(new_acc_atb);
          assert get_current_key_fp(acc_atb) == none;
          if (mem(zero, get_just_tails(acc_atb)))
            nozero_no_current_key(acc_atb);

        } else {
          get_key_none_no_chain(advance_acc(acc_atb), t, dist - 1);
          advance_acc_keeps_tail_mem(acc_atb, nat_of_int(dist - 1));
          assert true == distinct(get_just_tails(new_acc_atb));
          acc_add_chain_buckets_ok_rec(advance_acc(acc_atb),
                                       t, k, dist - 1, bound);
          assert advance_acc(new_acc_atb) ==
                 cons(pair(k, nat_of_int(dist - 1)), advance_acc(acc_atb));
          assert true == buckets_ok_rec(advance_acc(new_acc_atb), t, bound);
        }
    }
  }
  @*/

/*@
  lemma void short_buckets_put_still_ok_rec<kt>(list<pair<kt, nat> > acc,
                                                list<bucket<kt> > buckets,
                                                kt k, int start, int dist,
                                                int bound)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*& dist < bound &*&
           start + dist < length(buckets) &*&
           length(buckets) <= bound &*&
           true == buckets_short_fp(buckets) &*&
           nth(start + dist, buckets_get_keys_rec_fp(acc, buckets)) == none;
  ensures true == buckets_ok_rec(acc, buckets_put_key_fp(buckets, k, start,
                                                         dist),
                                 bound);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > new_acc_atb =
            acc_at_this_bucket(acc, bucket_put_key_fp(h, k, dist));

          acc_at_bucket_put_is_cons(acc, h, k, dist);
          assert true == set_eq(cons(pair(k, nat_of_int(dist)),
                                         acc_atb),
                                    new_acc_atb);
          assert true == forall(cons(pair(k, nat_of_int(dist)), acc_atb),
                                (upper_limit)(bound));
          set_eq_forall_both(cons(pair(k, nat_of_int(dist)), acc_atb),
                                 new_acc_atb, (upper_limit)(bound));
          assert true == forall(new_acc_atb, (upper_limit)(bound));
          assert true == distinct(get_just_tails(acc_atb));
          if (dist == 0) {
            assert get_current_key_fp(acc_atb) == none;
            if (mem(zero, get_just_tails(acc_atb)))
              nozero_no_current_key(acc_atb);
            assert false == mem(zero, get_just_tails(acc_atb));
            assert true == distinct(get_just_tails(acc_atb));
            assert true == distinct(get_just_tails(cons(pair(k, zero), acc_atb)));

            accs_eq_tails_distinct(cons(pair(k, zero), acc_atb),
                                   new_acc_atb);
            assert advance_acc(cons(pair(k, zero), acc_atb)) ==
                   advance_acc(acc_atb);
            advance_acc_still_eq(cons(pair(k, zero), acc_atb),
                                        new_acc_atb);
            advance_acc_still_distinct(new_acc_atb);
            acc_eq_buckets_ok_rec(advance_acc(acc_atb),
                                  advance_acc(new_acc_atb),
                                  t, bound);
          } else {
            get_key_none_no_chain(advance_acc(acc_atb), t, dist - 1);
            assert false == mem(nat_of_int(dist - 1), get_just_tails(advance_acc(acc_atb)));
            advance_acc_keeps_tail_mem(acc_atb, nat_of_int(dist - 1));
            assert false == mem(nat_of_int(dist), get_just_tails(acc_atb));
            assert true == distinct(get_just_tails(cons(pair(k, nat_of_int(dist)), acc_atb)));
            assert length(cons(pair(k, nat_of_int(dist)), acc_atb)) ==
                          length(new_acc_atb);

            accs_eq_tails_distinct(cons(pair(k, nat_of_int(dist)), acc_atb),
                                   new_acc_atb);
            assert true == distinct(get_just_tails(new_acc_atb));
            assert advance_acc(cons(pair(k, nat_of_int(dist)), acc_atb)) ==
                   cons(pair(k, nat_of_int(dist - 1)), advance_acc(acc_atb));
            acc_add_chain_buckets_ok_rec(advance_acc(acc_atb),
                                         t, k, dist - 1, bound);
            assert true == buckets_ok_rec
                             (advance_acc(cons(pair(k, nat_of_int(dist)),
                                               acc_atb)),
                              t, bound);
            advance_acc_still_eq(cons(pair(k, nat_of_int(dist)),
                                             acc_atb),
                                        new_acc_atb);
            advance_acc_still_distinct(new_acc_atb);
            acc_eq_buckets_ok_rec(advance_acc(cons(pair(k, nat_of_int(dist)),
                                                   acc_atb)),
                                  advance_acc(new_acc_atb),
                                  t, bound);
          }
        } else {
          switch(h) { case bucket(chains): }
          short_buckets_put_still_ok_rec(advance_acc(acc_at_this_bucket(acc, h)),
                                         t, k, start - 1, dist, bound);
        }
    }
  }
  @*/


/*@
  lemma void filter_zero_lower_limit_no_effect<kt>(list<pair<kt, nat> > acc)
  requires true;
  ensures filter((lower_limit)(0), acc) == acc;
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
          filter_zero_lower_limit_no_effect(t);
        }
    }
  }
  @*/

/*@
  lemma void advance_acc_filter_keep_long_swap<kt>(list<pair<kt, nat> > acc,
                                                   int cutoff)
  requires 0 < cutoff;
  ensures advance_acc(filter((lower_limit)(cutoff), acc)) ==
          filter((lower_limit)(cutoff-1), advance_acc(acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
          advance_acc_filter_keep_long_swap(t, cutoff);
        }
    }
  }
  @*/

/*@
  lemma void filter_acc_keep_wraparound<kt>(list<pair<kt, nat> > acc,
                                            list<bucket<kt> > buckets)
  requires true;
  ensures get_wraparound(acc, buckets) ==
          get_wraparound(filter((lower_limit)(length(buckets)), acc), buckets);
  {
    switch(buckets) {
      case nil:
        filter_zero_lower_limit_no_effect(acc);
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > f_atb =
            append(filter((lower_limit)(length(buckets)), acc), chains);
          list<pair<kt, nat> > filt_all_atb =
            append(filter((lower_limit)(length(buckets)), acc),
                   filter((lower_limit)(length(buckets)), chains));
          filter_append_idemp(acc, chains, (lower_limit)(length(buckets)));
          filter_append_idemp(filter((lower_limit)(length(buckets)), acc),
                              chains,
                              (lower_limit)(length(buckets)));
          filter_forall((lower_limit)(length(buckets)), acc);
          filter_forall((lower_limit)(length(buckets)),
                        filter((lower_limit)(length(buckets)), acc));
          assert filter((lower_limit)(length(buckets)), atb) ==
                 filt_all_atb;
          assert filt_all_atb ==
                 append(filter((lower_limit)(length(buckets)), filter((lower_limit)(length(buckets)), acc)),
                        filter((lower_limit)(length(buckets)), chains));
          assert filter((lower_limit)(length(buckets)), filter((lower_limit)(length(buckets)), acc)) ==
                 filter((lower_limit)(length(buckets)), acc);
          assert filter((lower_limit)(length(buckets)), f_atb) ==
                 filt_all_atb;
          advance_acc_filter_keep_long_swap(atb, length(buckets));
          advance_acc_filter_keep_long_swap(f_atb, length(buckets));
          assert filter((lower_limit)(length(t)), advance_acc(atb)) ==
                 advance_acc(filt_all_atb);
          assert filter((lower_limit)(length(t)), advance_acc(f_atb)) ==
                 advance_acc(filt_all_atb);
          filter_acc_keep_wraparound(advance_acc(atb), t);
          filter_acc_keep_wraparound(advance_acc(f_atb), t);
        }
    }
  }//took 30m
  @*/

/*@
  lemma void keep_long_same_wraparound<kt>(list<pair<kt, nat> > acc,
                                           list<bucket<kt> > buckets)
  requires true;
  ensures get_wraparound(acc, keep_long_fp(buckets)) ==
          get_wraparound(acc, buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > filter_acc =
          filter((lower_limit)(length(buckets)), acc);
        filter_acc_keep_wraparound(acc, buckets);
        filter_acc_keep_wraparound(acc, keep_long_fp(buckets));
        keep_long_same_len(buckets);
        filter_forall((lower_limit)(length(buckets)), acc);
        switch(h) {case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(filter_acc, h);
          list<pair<kt, nat> > long_atb =
            append(filter_acc, filter((lower_limit)(length(buckets)),
                                      chains));
          filter_append_idemp(filter_acc, chains,
                              (lower_limit)(length(buckets)));
          filter_forall((lower_limit)(length(buckets)), filter_acc);
          assert long_atb == filter((lower_limit)(length(buckets)), atb);
          filter_acc_keep_wraparound(advance_acc(atb), t);
          advance_acc_filter_keep_long_swap(atb, length(buckets));
          keep_long_same_wraparound(advance_acc(long_atb), t);
        }
    }
  }
  @*/

/*@

  lemma void
  buckets_put_short_chain_same_wraparound<kt>(list<pair<kt, nat> > acc,
                                              list<bucket<kt> > buckets,
                                              kt k, int start, int dist,
                                              int capacity)
  requires 0 <= start &*& start < length(buckets) &*&
           start + dist < length(buckets) &*&
           0 <= dist;
  ensures get_wraparound(acc, buckets_put_key_fp(buckets, k, start,
                                                 dist)) ==
          get_wraparound(acc, buckets);
  {

    keep_long_same_wraparound(acc, buckets);
    keep_long_same_wraparound(acc, buckets_put_key_fp(buckets, k, start, dist));
    buckets_put_key_keep_long_no_effect(buckets, k, start, dist);
  }
  @*/

/*@
  lemma void buckets_put_key_keep_short_no_effect<kt>(list<bucket<kt> >buckets,
                                                      kt k, int start, int dist)
  requires length(buckets) <= start + dist;
  ensures keep_short_fp(buckets_put_key_fp(buckets, k, start, dist)) ==
          keep_short_fp(buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_put_same_len(buckets, k, start, dist);
        switch(h) { case bucket(chains):
          if (start == 0) {
            assert filter((upper_limit)(length(buckets)), chains) ==
                   filter((upper_limit)(length(buckets)),
                          cons(pair(k, nat_of_int(dist)), chains));
          } else {
            buckets_put_key_keep_short_no_effect(t, k, start - 1, dist);
          }
        }
    }
  }//took 3m

  lemma void buckets_put_key_keep_long_swap<kt>(list<bucket<kt> > buckets,
                                                kt k, int start, int dist)
  requires length(buckets) <= start + dist;
  ensures keep_long_fp(buckets_put_key_fp(buckets, k, start, dist)) ==
          buckets_put_key_fp(keep_long_fp(buckets), k, start, dist);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        buckets_put_same_len(buckets, k, start, dist);
        switch(h) { case bucket(chains):
          if (start == 0) {
            assert cons(pair(k, nat_of_int(dist)),
                        filter((lower_limit)(length(buckets)), chains)) ==
                   filter((lower_limit)(length(buckets)),
                          cons(pair(k, nat_of_int(dist)), chains));
          } else {
            buckets_put_key_keep_long_swap(t, k, start - 1, dist);
          }
        }
    }
  }//took 15m
  @*/


/*@
  lemma void advance_acc_dec_mem<kt>(list<pair<kt, nat> > acc, nat n)
  requires true;
  ensures mem(n, get_just_tails(advance_acc(acc))) ==
          mem(succ(n), get_just_tails(acc));
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
            case succ(m):
          }
          advance_acc_dec_mem(t, n);
        }
    }
  }
  @*/


/*@
  lemma void no_chain_in_wraparound_not_here<kt>(list<pair<kt, nat> > acc,
                                                 list<bucket<kt> > buckets,
                                                 int dist)
  requires false == mem(nat_of_int(dist - length(buckets)),
                        get_just_tails(get_wraparound(acc, buckets))) &*&
           length(buckets) <= dist;
  ensures false == mem(nat_of_int(dist), get_just_tails(acc));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
        no_chain_in_wraparound_not_here(advance_acc(atb), t, dist - 1);
        assert false == mem(nat_of_int(dist - 1),
                            get_just_tails(advance_acc(atb)));
        if (mem(nat_of_int(dist), get_just_tails(acc))) {
          switch(h) { case bucket(chains):
            map_append(snd, acc, chains);
            mem_append(nat_of_int(dist), get_just_tails(acc), get_just_tails(chains));
            assert true == mem(nat_of_int(dist), get_just_tails(atb));
          }
          assert succ(nat_of_int(dist - 1)) == nat_of_int(dist);
          advance_acc_dec_mem(atb, nat_of_int(dist - 1));
          assert true == mem(nat_of_int(dist - 1),
                             get_just_tails(advance_acc(atb)));

          assert false;
        }
    }
  }//took 15m
  @*/

/*@
  lemma void
  acc_add_chain_abscent_in_wraparound_buckets_ok_rec<kt>
    (list<pair<kt, nat> > acc,
     list<bucket<kt> > buckets,
     kt k, int dist,
     int bound)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           length(buckets) <= dist &*& dist < bound - 1 &*&
           false == mem(nat_of_int(dist - length(buckets)),
                        get_just_tails(get_wraparound(acc, buckets)));
  ensures true == buckets_ok_rec(cons(pair(k, nat_of_int(dist)), acc),
                                 buckets, bound);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
        list<pair<kt, nat> > new_acc_atb =
          acc_at_this_bucket(cons(pair(k, nat_of_int(dist)), acc), h);
        cons_acc_atb_swap(acc, h, pair(k, nat_of_int(dist)));
        assert new_acc_atb == cons(pair(k, nat_of_int(dist)), acc_atb);
        assert true == forall(new_acc_atb, (upper_limit)(bound));
        no_chain_in_wraparound_not_here(advance_acc(acc_atb), t, dist-1);
        advance_acc_keeps_tail_mem(acc_atb, nat_of_int(dist - 1));
        assert true == distinct(get_just_tails(new_acc_atb));
        acc_add_chain_abscent_in_wraparound_buckets_ok_rec
          (advance_acc(acc_atb),
           t, k, dist - 1, bound);
        assert advance_acc(new_acc_atb) ==
                cons(pair(k, nat_of_int(dist - 1)),
                     advance_acc(acc_atb));
        assert true == buckets_ok_rec(advance_acc(new_acc_atb), t, bound);
    }
  }
  @*/

/*@
  lemma void long_buckets_put_still_ok_rec<kt>(list<pair<kt, nat> > acc,
                                               list<bucket<kt> > buckets,
                                               kt k, int start, int dist,
                                               int bound)
  requires true == buckets_ok_rec(acc, buckets, bound) &*&
           true == buckets_long_fp(buckets) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*& dist < bound &*&
           length(buckets) <= start + dist &*&
           false == mem(nat_of_int(start + dist - length(buckets)),
                        get_just_tails(get_wraparound(acc, buckets)));
  ensures true == buckets_ok_rec(acc, buckets_put_key_fp(buckets, k,
                                                         start, dist),
                                 bound);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        if (start == 0) {
          list<pair<kt, nat> > acc_atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > new_acc_atb =
            acc_at_this_bucket(acc, bucket_put_key_fp(h, k, dist));
          acc_at_bucket_put_is_cons(acc, h, k, dist);
          assert true == forall(cons(pair(k, nat_of_int(dist)), acc_atb),
                                (upper_limit)(bound));
          set_eq_forall_both(cons(pair(k, nat_of_int(dist)), acc_atb),
                                 new_acc_atb,
                                 (upper_limit)(bound));
          assert true == forall(new_acc_atb, (upper_limit)(bound));
          assert true == distinct(get_just_tails(acc_atb));
          no_chain_in_wraparound_not_here(advance_acc(acc_atb), t, dist-1);
          assert false == mem(nat_of_int(dist-1),
                              get_just_tails(advance_acc(acc_atb)));
          advance_acc_keeps_tail_mem(acc_atb, nat_of_int(dist - 1));
          assert false == mem(nat_of_int(dist), get_just_tails(acc_atb));
          assert length(cons(pair(k, nat_of_int(dist)), acc_atb)) ==
                 length(new_acc_atb);

          accs_eq_tails_distinct(cons(pair(k, nat_of_int(dist)), acc_atb),
                                 new_acc_atb);
          assert true == distinct(get_just_tails(new_acc_atb));
          acc_add_chain_abscent_in_wraparound_buckets_ok_rec
            (advance_acc(acc_atb), t, k, dist - 1, bound);
          advance_acc_still_eq(cons(pair(k, nat_of_int(dist)), acc_atb),
                               new_acc_atb);
          advance_acc_still_distinct(new_acc_atb);
          acc_eq_buckets_ok_rec(advance_acc(cons(pair(k, nat_of_int(dist)),
                                                 acc_atb)),
                                advance_acc(new_acc_atb),
                                t, bound);
          assert true == buckets_ok_rec(advance_acc(new_acc_atb), t, bound);
        } else {
          switch(h) { case bucket(chains):
            long_buckets_put_still_ok_rec
              (advance_acc(acc_at_this_bucket(acc, h)),
               t, k, start - 1, dist, bound);
          }
        }
    }
  }
  @*/

/*@
  lemma void
  acc_bounded_still_no_chain_in_wraparound<kt>
    (list<pair<kt, nat> > acc,
     list<pair<kt, nat> > more_acc,
     list<bucket<kt> > buckets,
     nat chain)
  requires false == mem(chain, get_just_tails
                                 (get_wraparound(acc,
                                                 buckets))) &*&
           true == forall(more_acc, (upper_limit)(length(buckets) - 1));
  ensures false == mem(chain, get_just_tails
                                (get_wraparound(append(more_acc, acc),
                                                buckets)));
  {
    short_chains_dont_matter(more_acc, acc, buckets, length(buckets) - 1,
                             length(buckets) - 1);
    wraparound_is_last_crossing_chains(acc, buckets);
    wraparound_is_last_crossing_chains(append(more_acc, acc), buckets);
  }
  @*/

/*@
  lemma void
  content_eq_same_mem_wraparound<kt>(list<pair<kt, nat> > acc1,
                                     list<pair<kt, nat> > acc2,
                                     list<bucket<kt> > buckets,
                                     nat chain)
  requires true == set_eq(acc1, acc2);
  ensures mem(chain, get_just_tails(get_wraparound(acc1, buckets))) ==
          mem(chain, get_just_tails(get_wraparound(acc2, buckets)));
  {
    switch(buckets) {
      case nil:
        content_eq_map(acc1, acc2, snd);
        if (mem(chain, get_just_tails(get_wraparound(acc1, buckets)))) {
          subset_mem_trans(get_just_tails(acc1), get_just_tails(acc2), chain);
        }
        if (mem(chain, get_just_tails(get_wraparound(acc2, buckets)))) {
          subset_mem_trans(get_just_tails(acc2), get_just_tails(acc1), chain);
        }
      case cons(h,t):
        list<pair<kt, nat> > atb1 = acc_at_this_bucket(acc1, h);
        list<pair<kt, nat> > atb2 = acc_at_this_bucket(acc2, h);
        acc_at_this_bucket_still_eq(acc1, acc2, h);
        advance_acc_still_eq(atb1, atb2);
        content_eq_same_mem_wraparound(advance_acc(atb1), advance_acc(atb2),
                                       t, chain);
    }
  }//took 5m
  @*/

/*@
  lemma void keep_long_indeed_long<kt>(list<bucket<kt> > buckets)
  requires true;
  ensures true == buckets_long_fp(keep_long_fp(buckets));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        keep_long_same_len(buckets);
        switch(h) { case bucket(chains):
          filter_forall((lower_limit)(length(buckets)), chains);
          assert keep_long_fp(buckets) ==
                 cons(bucket(filter((lower_limit)(length(buckets)), chains)),
                      keep_long_fp(t));
          assert true == forall(filter((lower_limit)(length(buckets)), chains),
                                (lower_limit)(length(buckets)));
          keep_long_indeed_long(t);
          assert true == buckets_long_fp(keep_long_fp(t));
          assert true == buckets_long_fp(cons(bucket(filter((lower_limit)(length(buckets)), chains)),
                                              keep_long_fp(t)));
        }
    }
  }
  @*/

/*@

  lemma void buckets_put_still_ok<kt>(list<bucket<kt> > buckets,
                                      kt k, int start, int dist)
  requires true == buckets_ok(buckets) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*& dist < length(buckets) &*&
           nth(loop_fp(start + dist, length(buckets)),
               buckets_get_keys_fp(buckets)) == none;
  ensures true == buckets_ok(buckets_put_key_fp(buckets, k, start, dist));
  {
    buckets_put_same_len(buckets, k, start, dist);
    if (length(buckets) <= start + dist) {
      assert true == buckets_ok_rec(get_wraparound(nil, buckets), buckets, length(buckets));
      buckets_put_wraparound_is_cons(nil, buckets, k, start, dist);
      loop_injection_n(start + dist - length(buckets), length(buckets), 1);
      loop_bijection(start + dist - length(buckets), length(buckets));
      acc_add_chain_buckets_ok_rec(get_wraparound(nil, buckets),
                                   buckets,
                                   k, start + dist - length(buckets),
                                   length(buckets));
      buckets_ok_rec_wraparound_distinct(get_wraparound(nil, buckets),
                                         buckets, length(buckets));
      buckets_ok_get_wraparound_idemp(buckets);
      assert true == distinct(get_just_tails(get_wraparound(nil, buckets)));
      nat dist_left = nat_of_int(start + dist - length(buckets));
      get_key_none_no_chain(get_wraparound(nil, buckets), buckets,
                            start + dist - length(buckets));
      assert false == mem(dist_left,
                          get_just_tails(get_wraparound(nil, buckets)));
      accs_eq_tails_distinct
        (cons(pair(k, nat_of_int(start + dist - length(buckets))),
              get_wraparound(nil, buckets)),
         get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)));
      acc_eq_buckets_ok_rec(cons(pair(k, nat_of_int(start + dist - length(buckets))),
                                 get_wraparound(nil, buckets)),
                            get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
                            buckets,
                            length(buckets));
      assert true == buckets_ok_rec(get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)), buckets, length(buckets));
      buckets_ok_short_long_ok
        (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
         buckets, length(buckets));
      buckets_put_key_keep_short_no_effect(buckets, k, start, dist);
      buckets_put_key_keep_long_swap(buckets, k, start, dist);
      keep_long_indeed_long(buckets);
      keep_long_same_len(buckets);
      buckets_put_wraparound_is_cons(nil, buckets, k, start, dist);
      assert true == set_eq
        (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
         cons(pair(k, nat_of_int(start + dist - length(buckets))),
              get_wraparound(nil, buckets)));
      buckets_ok_wraparound_bounded(buckets);
      assert true == forall(get_wraparound(nil, buckets),
                            (upper_limit)(length(buckets) - 1));
      assert true == forall(cons(pair(k, dist_left),
                                 get_wraparound(nil, buckets)),
                            (upper_limit)(length(buckets) - 1));
      acc_bounded_still_no_chain_in_wraparound
        (nil,
         cons(pair(k, dist_left), get_wraparound(nil, buckets)),
         buckets,
         dist_left);
      assert append(cons(pair(k, dist_left), get_wraparound(nil, buckets)), nil) ==
             cons(pair(k, dist_left), get_wraparound(nil, buckets));
      assert false == mem(dist_left,
                          get_just_tails
                            (get_wraparound(cons(pair(k, dist_left),
                                              get_wraparound(nil, buckets)), buckets)));
      content_eq_same_mem_wraparound
        (cons(pair(k, dist_left), get_wraparound(nil, buckets)),
         get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
         buckets,
         dist_left);
      assert false == mem(dist_left,
                          get_just_tails(
                            get_wraparound
                              (get_wraparound(nil, buckets_put_key_fp(buckets,
                                                                      k, start,
                                                                      dist)),
                               buckets)));
      keep_long_same_wraparound
        (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
         buckets);
      long_buckets_put_still_ok_rec
        (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
         keep_long_fp(buckets), k, start, dist, length(buckets));
      buckets_split_ok_orig_ok(get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
                               buckets_put_key_fp(buckets, k, start, dist),
                               length(buckets));
    } else {
      buckets_put_short_chain_same_wraparound(nil, buckets, k,
                                              start, dist,
                                              length(buckets));
      assert get_wraparound(nil, buckets_put_key_fp(buckets, k,
                                                    start, dist)) ==
             get_wraparound(nil, buckets);
      buckets_ok_short_long_ok
         (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
          buckets, length(buckets));
      keep_short_indeed_short(buckets);
      keep_short_same_len(buckets);
      loop_bijection(start + dist, length(buckets));
      no_key_especially_in_short_and_long
        (get_wraparound(nil, buckets_put_key_fp(buckets, k, start,
                                                dist)),
         buckets,
         start + dist);
      short_buckets_put_still_ok_rec
        (get_wraparound(nil, buckets_put_key_fp(buckets, k, start,
                                                dist)),
         keep_short_fp(buckets), k, start, dist, length(buckets));
      buckets_put_key_keep_short_swap(buckets, k, start, dist);
      buckets_put_key_keep_long_no_effect(buckets, k, start, dist);
      buckets_split_ok_orig_ok(get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
                                   buckets_put_key_fp(buckets, k, start, dist), length(buckets));
      assert true == buckets_ok_rec(get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
                                    buckets_put_key_fp(buckets, k, start, dist),
                                    length(buckets));
      assert true == buckets_ok_rec(get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
                                    buckets_put_key_fp(buckets, k, start, dist),
                                    length(buckets_put_key_fp(buckets, k, start, dist)));
    }
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
  lemma void cons_content_eq_this_cur_key<kt>(list<pair<kt, nat> > acc1,
                                              list<pair<kt, nat> > acc2,
                                              kt k)
  requires true == set_eq(cons(pair(k, zero), acc1), acc2) &*&
           true == distinct(get_just_tails(acc2));
  ensures get_current_key_fp(acc2) == some(k);
  {
    subset_mem_trans(cons(pair(k, zero), acc1), acc2, pair(k, zero));
    distinct_and_zero_this_is_the_key(acc2, k);
  }
  @*/


/*@
  lemma void remove_chain_get_current_key<kt>(list<pair<kt, nat> > acc,
                                              kt k, nat dst)
  requires dst != zero;
  ensures get_current_key_fp(remove(pair(k, dst), acc)) ==
          get_current_key_fp(acc);
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
              if (h != pair(k, dst))
                remove_chain_get_current_key(t, k, dst);
          }
        }
    }
  }
  @*/

/*@
  lemma void acc_eq_same_cur_key<kt>(list<pair<kt, nat> > acc1,
                                     list<pair<kt, nat> > acc2)
  requires true == distinct(get_just_tails(acc1)) &*&
           true == distinct(get_just_tails(acc2)) &*&
           true == set_eq(acc1, acc2);
  ensures get_current_key_fp(acc1) == get_current_key_fp(acc2);
  {
    switch(acc1) {
      case nil:
        subset_nil_nil(acc2);
      case cons(h,t):
        switch(h) { case pair(key, dist):
          switch(dist) {
            case zero:
              subset_mem_trans(acc1, acc2, h);
              distinct_and_zero_this_is_the_key(acc2, key);
            case succ(n):
              distinct_unmap(acc1, snd);
              distinct_unmap(acc2, snd);
              set_eq_remove_both(acc1, acc2, h);
              distinct_map_remove(acc2, snd, h);
              remove_chain_get_current_key(acc2, key, dist);
              acc_eq_same_cur_key(t, remove(h, acc2));
          }
        }
    }
  }
  @*/


/*@
  lemma void acc_eq_same_ks<kt>(list<pair<kt, nat> > acc1,
                                list<pair<kt, nat> > acc2,
                                list<bucket<kt> > buckets,
                                int bound)
  requires true == set_eq(acc1, acc2) &*&
           true == distinct(get_just_tails(acc2)) &*&
           true == buckets_ok_rec(acc1, buckets, bound);
  ensures buckets_get_keys_rec_fp(acc1, buckets) ==
          buckets_get_keys_rec_fp(acc2, buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb1 = acc_at_this_bucket(acc1, h);
        list<pair<kt, nat> > atb2 = acc_at_this_bucket(acc2, h);
        acc_at_this_bucket_still_eq(acc1, acc2, h);

        switch(h) { case bucket(chains):
          map_append(snd, acc1, chains);
          map_append(snd, acc2, chains);
          subset_map(acc2, acc1, snd);
          subset_append_distinct(get_just_tails(acc2),
                                 get_just_tails(acc1),
                                 get_just_tails(chains));
        }
        assert true == distinct(get_just_tails(atb1));
        assert true == distinct(get_just_tails(atb2));
        acc_eq_same_cur_key(atb1, atb2);
        assert get_current_key_fp(atb1) ==
               get_current_key_fp(atb2);
        advance_acc_still_eq(atb1, atb2);
        assert true == set_eq(advance_acc(atb1), advance_acc(atb2));
        advance_acc_still_distinct(atb2);
        acc_eq_same_ks(advance_acc(atb1), advance_acc(atb2),
                       t, bound);
    }
  }
  @*/



/*@
  lemma void single_elem_cur_key_is_none<kt>(list<pair<kt, nat> > acc,
                                             kt k, nat dst)
  requires true == subset(acc, cons(pair(k, dst), nil)) &*&
           dst != zero;
  ensures get_current_key_fp(acc) == none;
  {
    switch(acc) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,dist):
          switch(dist) {
            case zero:
            case succ(n):
          }
        }
        assert h == pair(k, dst);
        single_elem_cur_key_is_none(t, k, dst);
    }
  }
  @*/

/*@
  lemma void cons_content_eq_same_cur_key<kt>(list<pair<kt, nat> > acc1,
                                              list<pair<kt, nat> > acc2,
                                              kt k, nat dst)
  requires true == set_eq(cons(pair(k, dst), acc1), acc2) &*&
           false == mem(dst, get_just_tails(acc1)) &*&
           true == distinct(get_just_tails(acc2)) &*&
           true == distinct(get_just_tails(acc1)) &*&
           dst != zero;
  ensures get_current_key_fp(acc1) == get_current_key_fp(acc2);
  {
      switch(acc1) {
        case nil:
          single_elem_cur_key_is_none(acc2, k, dst);
        case cons(h,t):
          switch(h) { case pair(key,dist):
            switch(dist) {
              case zero:
                assert true == mem(h, acc2);
                distinct_and_zero_this_is_the_key(acc2, key);
              case succ(n):
                distinct_map_remove(acc2, snd, h);
                assert remove(h, cons(pair(k, dst), acc1)) ==
                       cons(pair(k, dst), t);
                distinct_unmap(acc1, snd);
                distinct_unique(acc1, h);
                distinct_unmap(acc2, snd);
                distinct_unique(acc2, h);
                if (h == pair(k, dst)) {
                  assert true == mem(dst, get_just_tails(acc1));
                }
                assert false == mem(h, remove(h, cons(pair(k, dst), acc1)));
                set_eq_remove_uniq_both(cons(pair(k, dst), acc1), acc2, h);
                cons_content_eq_same_cur_key(t, remove(h, acc2), k, dst);
                remove_chain_get_current_key(acc2, key, dist);
            }
          }
      }
  }//took 40m
  @*/


/*@
  lemma void acc_eq_cons_update_ks<kt>(list<pair<kt, nat> > acc1,
                                       list<pair<kt, nat> > acc2,
                                       list<bucket<kt> > buckets,
                                       kt k,
                                       int dist,
                                       int bound)
  requires true == set_eq(cons(pair(k, nat_of_int(dist)), acc1), acc2) &*&
           0 <= dist &*& dist < length(buckets) &*&
           nth(dist, buckets_get_keys_rec_fp(acc1, buckets)) == none &*&
           true == buckets_ok_rec(acc1, buckets, bound) &*&
           length(acc1) + 1 == length(acc2);
  ensures buckets_get_keys_rec_fp(acc2, buckets) ==
          update(dist, some(k), buckets_get_keys_rec_fp(acc1, buckets));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb1 = acc_at_this_bucket(acc1, h);
        list<pair<kt, nat> > atb2 = acc_at_this_bucket(acc2, h);
        cons_acc_atb_swap(acc1, h, pair(k, nat_of_int(dist)));
        acc_at_this_bucket_still_eq(cons(pair(k, nat_of_int(dist)), acc1),
                                    acc2,
                                    h);
        assert true == set_eq(cons(pair(k, nat_of_int(dist)), atb1),
                                  atb2);
        switch(h) { case bucket(chains):
          assert length(atb1) + 1 == length(atb2);
        }
        assert length(atb1) + 1 == length(atb2);
        if (dist == 0) {
          nozero_no_current_key(atb1);
        } else {
          get_key_none_no_chain(advance_acc(atb1), t, dist - 1);
          advance_acc_keeps_tail_mem(atb1, nat_of_int(dist-1));
        }
        accs_eq_tails_distinct(cons(pair(k, nat_of_int(dist)), atb1), atb2);
        advance_acc_still_eq(cons(pair(k, nat_of_int(dist)), atb1), atb2);
        advance_acc_still_distinct(atb2);

        if (dist == 0) {
          assert true == set_eq(advance_acc(atb1), advance_acc(atb2));
          cons_content_eq_this_cur_key(atb1, atb2, k);
          acc_eq_same_ks(advance_acc(atb1), advance_acc(atb2), t, bound);
        } else {
          cons_content_eq_same_cur_key(atb1, atb2, k, nat_of_int(dist));
          assert get_current_key_fp(cons(pair(k, nat_of_int(dist)), atb1)) ==
                 get_current_key_fp(atb2);
          assert true == distinct(get_just_tails(atb1));
          assert true == distinct(get_just_tails(atb2));
          if (mem(pair(k, nat_of_int(dist)), atb1)) {
            mem_map(pair(k, nat_of_int(dist)), atb1, snd);
            assert true == mem(nat_of_int(dist), get_just_tails(atb2));
            assert false;
          }
          distinct_unmap(atb1, snd);
          assert true == distinct(atb1);
          assert true == distinct(cons(pair(k, nat_of_int(dist)), atb1));
          advance_acc_still_distinct(cons(pair(k, nat_of_int(dist)), atb1));
          advance_acc_still_distinct(atb2);
          distinct_unmap
            (advance_acc(cons(pair(k, nat_of_int(dist)), atb1)), snd);
          distinct_unmap
            (advance_acc(atb2), snd);
          set_eq_distinct_same_len
            (advance_acc(cons(pair(k, nat_of_int(dist)), atb1)),
             advance_acc(atb2));
          assert length(advance_acc(cons(pair(k, nat_of_int(dist)), atb1))) ==
                 length(advance_acc(atb2));
          acc_eq_cons_update_ks(advance_acc(atb1), advance_acc(atb2),
                                t, k, dist - 1, bound);
        }
    }
  }//took 90m + 4 more lemmas
  @*/

/*@
  lemma void bucket_put_update_ks_nowraparound<kt>(list<pair<kt, nat> > acc,
                                                   list<bucket<kt> > buckets,
                                                   list<option<kt> > ks,
                                                   kt k, int start, int dist,
                                                   int bound)
  requires ks == buckets_get_keys_rec_fp(acc, buckets) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*& start + dist < length(buckets) &*&
           true == buckets_ok_rec(acc, buckets, bound) &*&
           nth(start + dist, buckets_get_keys_rec_fp(acc, buckets)) == none;
  ensures update(start + dist, some(k), ks) ==
          buckets_get_keys_rec_fp(acc, buckets_put_key_fp(buckets, k,
                                                          start, dist));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
        assert ks == cons(?ksh,?kst);
        if (start == 0) {
          list<pair<kt, nat> > new_atb =
            acc_at_this_bucket(acc,bucket_put_key_fp(h, k, dist));
          acc_at_bucket_put_is_cons(acc, h, k, dist);
          if (dist == 0) {
            nozero_no_current_key(atb);
          } else {
            get_key_none_no_chain(advance_acc(atb), t, dist - 1);
            advance_acc_keeps_tail_mem(atb, nat_of_int(dist-1));
          }
          accs_eq_tails_distinct(cons(pair(k, nat_of_int(dist)), atb), new_atb);
          assert true == distinct(get_just_tails(new_atb));
          advance_acc_still_distinct(cons(pair(k, nat_of_int(dist)), atb));
          advance_acc_still_distinct(new_atb);
          advance_acc_still_eq(cons(pair(k, nat_of_int(dist)), atb), new_atb);
          if (dist == 0) {
            cons_content_eq_this_cur_key(atb, new_atb, k);
            acc_eq_same_ks(advance_acc(atb), advance_acc(new_atb), t, bound);
          } else {
            assert true == set_eq(advance_acc(cons(pair(k, nat_of_int(dist)), atb)), advance_acc(new_atb));
            assert succ(nat_of_int(dist-1)) == nat_of_int(dist);
            assert advance_acc((cons(pair(k, nat_of_int(dist)), atb))) ==
                   cons(pair(k, nat_of_int(dist-1)), advance_acc(atb));
            assert true == set_eq(cons(pair(k, nat_of_int(dist-1)), advance_acc(atb)), advance_acc(new_atb));
            switch(h) { case bucket(chains):
              assert length(atb) + 1 == length(new_atb);
            }
            assert false == mem(nat_of_int(dist), get_just_tails(atb));
            assert true == distinct(get_just_tails(cons(pair(k, nat_of_int(dist)), atb)));
            assert true == distinct(get_just_tails(atb));
            distinct_unmap(advance_acc(cons(pair(k, nat_of_int(dist)), atb)),
                           snd);
            distinct_unmap(advance_acc(new_atb), snd);
            set_eq_distinct_same_len
              (advance_acc(cons(pair(k, nat_of_int(dist)), atb)),
               advance_acc(new_atb));
            acc_eq_cons_update_ks(advance_acc(atb), advance_acc(new_atb),
                                  t, k, dist - 1, bound);
            cons_content_eq_same_cur_key(atb, new_atb, k, nat_of_int(dist));
            assert get_current_key_fp(atb) == get_current_key_fp(new_atb);
          }
        } else {
          bucket_put_update_ks_nowraparound(advance_acc(atb),
                                            t, kst, k, start - 1,
                                            dist, bound);
        }
    }
  }//took 95m
  @*/


/*@
  lemma void buckets_put_update_ks<kt>(list<bucket<kt> > buckets,
                                       list<option<kt> > ks,
                                       kt k, int start, int dist)
  requires ks == buckets_get_keys_fp(buckets) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*& dist < length(buckets) &*&
           true == buckets_ok(buckets) &*&
           nth(loop_fp(start + dist, length(buckets)), ks) == none;
  ensures update(loop_fp(start + dist, length(buckets)), some(k), ks) ==
          buckets_get_keys_fp(buckets_put_key_fp(buckets, k, start,
                                                 dist));
  {
    if (start + dist < length(buckets)) {
      loop_bijection(start + dist, length(buckets));
      buckets_put_short_chain_same_wraparound
        (nil, buckets, k,
         start, dist,
         length(buckets));
      bucket_put_update_ks_nowraparound
        (get_wraparound(nil, buckets), buckets,
         ks, k, start, dist,
         length(buckets));
    } else {
      loop_injection_n(start + dist - length(buckets), length(buckets), 1);
      loop_bijection(start + dist - length(buckets), length(buckets));
      buckets_short_get_keys_rec(get_wraparound(nil, buckets), buckets);
      assert buckets_get_keys_rec_fp(get_wraparound(nil, buckets), buckets) ==
             buckets_get_keys_rec_fp(get_wraparound(nil, buckets),
                                     keep_short_fp(buckets));
      list<bucket<kt> > bpt = buckets_put_key_fp(buckets, k, start, dist);
      buckets_put_key_keep_short_no_effect (buckets, k, start, dist);
      assert keep_short_fp(buckets) == keep_short_fp(bpt);
      buckets_short_get_keys_rec(get_wraparound(nil, bpt), bpt);
      assert buckets_get_keys_rec_fp(get_wraparound(nil, bpt),
                                     bpt) ==
             buckets_get_keys_rec_fp(get_wraparound(nil, bpt),
                                     keep_short_fp(bpt));
      assert buckets_get_keys_fp(bpt) ==
             buckets_get_keys_rec_fp(get_wraparound(nil, bpt),
                                     keep_short_fp(buckets));
      nat tail_left = nat_of_int(start + dist - length(buckets));
      buckets_put_wraparound_is_cons(nil, buckets, k, start, dist);
      assert true == set_eq(cons(pair(k, tail_left),
                                     get_wraparound(nil, buckets)),
                                get_wraparound(nil, bpt));
      keep_short_same_len(buckets);
      buckets_ok_short_long_ok(get_wraparound(nil, buckets),
                               buckets,
                               length(buckets));
      acc_eq_cons_update_ks(get_wraparound(nil, buckets),
                            get_wraparound(nil, bpt),
                            keep_short_fp(buckets),
                            k,
                            start + dist - length(buckets),
                            length(buckets));
    }
  }//took 15m+35m so far
  @*/


/*@
  lemma void advance_acc_eliminate_zero_chain<kt>(list<pair<kt, nat> > acc1,
                                                  list<pair<kt, nat> > acc2,
                                                  kt k)
  requires true;
  ensures advance_acc(append(acc1, cons(pair(k, zero), acc2))) ==
          advance_acc(append(acc1, acc2));
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
        advance_acc_eliminate_zero_chain(t, acc2, k);
    }
  }
  @*/


/*@
  lemma void add_no_partial_chain_rec(list<int> chns)
  requires true;
  ensures add_partial_chain_rec_fp(chns, 0, 0) == chns;
  {
    switch(chns) {
      case nil:
      case cons(h,t):
    }
  }
  @*/


/*@
  lemma void buckets_add_part_get_chns_norm_rec<kt>(list<pair<kt, nat> > acc,
                                                    list<bucket<kt> > buckets,
                                                    kt k, int start, int dist)
  requires start + dist <= length(buckets) &*&
           0 <= dist;
  ensures buckets_get_chns_rec_fp(acc, buckets_put_key_fp(buckets, k,
                                                          start, dist)) ==
          add_partial_chain_rec_fp(buckets_get_chns_rec_fp(acc, buckets),
                                   start, dist);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          if (start == 0) {
            list<pair<kt, nat> > new_atb =
              acc_at_this_bucket(acc, bucket_put_key_fp(h, k, dist));
            assert new_atb == append(acc, cons(pair(k, nat_of_int(dist)), chains));
            cons_in_the_middle_multiset_eq(acc, chains,
                                           pair(k, nat_of_int(dist)));
            assert true == multiset_eq(new_atb, cons(pair(k, nat_of_int(dist)), atb));
            assert length(new_atb) == length(atb) + 1;
            if (dist == 0) {
              advance_acc_eliminate_zero_chain(acc, chains, k);
              assert advance_acc(atb) == advance_acc(new_atb);
              add_no_partial_chain_rec(buckets_get_chns_rec_fp(advance_acc(atb), t));
              assert add_partial_chain_rec_fp(buckets_get_chns_rec_fp(advance_acc(atb), t), start, dist) == buckets_get_chns_rec_fp(advance_acc(atb), t);
            } else {
              advance_acc_multiset_eq(new_atb,
                                      cons(pair(k, nat_of_int(dist)), atb));
              nat m = nat_of_int(dist - 1);
              assert succ(m) == nat_of_int(dist);
              assert true == multiset_eq(advance_acc(new_atb),
                                         cons(pair(k, nat_of_int(dist-1)),
                                              advance_acc(atb)));
              multiset_eq_same_len(advance_acc(new_atb), cons(pair(k, nat_of_int(dist-1)), advance_acc(atb)));
              assert length(advance_acc(new_atb)) == length(advance_acc(atb)) + 1;
              acc_eq_cons_get_chns_like_add_part_chn(advance_acc(new_atb),
                                                     advance_acc(atb),
                                                     t, k, dist - 1);
            }
          } else {
            buckets_add_part_get_chns_norm_rec(advance_acc(atb),
                                               t, k, start - 1, dist);
          }
        }
    }
  }
  @*/

/*@
  lemma void buckets_add_part_get_chns_norm<kt>(list<bucket<kt> > buckets,
                                                kt k, int start, int dist)
  requires start + dist < length(buckets) &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist &*&
           true == buckets_ok(buckets);
  ensures buckets_get_chns_fp(buckets_put_key_fp(buckets, k,
                                                 start, dist)) ==
          add_partial_chain_fp(start, dist,
                               buckets_get_chns_fp(buckets));
  {
    buckets_put_short_chain_same_wraparound(nil, buckets,
                                            k, start, dist,
                                            length(buckets));
    buckets_add_part_get_chns_norm_rec(get_wraparound(nil, buckets),
                                       buckets, k, start, dist);
    buckets_keys_chns_same_len(buckets);
    buckets_put_same_len(buckets, k, start, dist);
    buckets_keys_chns_same_len(buckets_put_key_fp(buckets, k, start, dist));
  }//took 200m
  @*/

/*@
  lemma void
  buckets_put_chain_lim_wraparound_add_zero_chain<kt>(list<pair<kt, nat> > acc,
                                                      list<bucket<kt> > buckets,
                                                      kt k, int start)
  requires 0 <= start &*& start < length(buckets);
  ensures true == multiset_eq
                    (get_wraparound(acc, buckets_put_key_fp(buckets,
                                                            k, start,
                                                            length(buckets) -
                                                              start)),
                     cons(pair(k, zero), get_wraparound(acc, buckets)));
  {
    buckets_put_wraparound_eq_cons(acc, buckets, k, start,
                                   length(buckets) - start);
  }
  @*/


/*@
  lemma void buckets_add_part_get_chns_lim<kt>(list<bucket<kt> > buckets,
                                               kt k, int start)
  requires 0 <= start &*& start < length(buckets) &*&
           true == buckets_ok(buckets);
  ensures buckets_get_chns_fp(buckets_put_key_fp(buckets, k,
                                                 start,
                                                 length(buckets) - start)) ==
          add_partial_chain_fp(start, length(buckets) - start,
                               buckets_get_chns_fp(buckets));
  {
    int dist = length(buckets) - start;
    buckets_keys_chns_same_len(buckets);
    buckets_put_same_len(buckets, k, start, dist);
    buckets_keys_chns_same_len(buckets_put_key_fp(buckets, k, start, dist));

    buckets_put_chain_lim_wraparound_add_zero_chain(nil, buckets, k, start);

    assert true == multiset_eq
       (get_wraparound(nil, buckets_put_key_fp(buckets, k, start,
                                               length(buckets) - start)),
        cons(pair(k, zero), get_wraparound(nil, buckets)));
    acc_additional_zero_chain_same_chns
      (get_wraparound(nil, buckets_put_key_fp(buckets, k, start,
                                              length(buckets) - start)),
       get_wraparound(nil, buckets),
       buckets, k);
    buckets_add_part_get_chns_norm_rec(get_wraparound(nil, buckets),
                                       buckets, k, start,
                                       length(buckets) - start);
    acc_additional_zero_chain_same_chns
      (get_wraparound(nil, buckets_put_key_fp(buckets, k, start,
                                              length(buckets) - start)),
       get_wraparound(nil, buckets),
       buckets_put_key_fp(buckets, k, start, length(buckets) - start), k);
  }
  @*/


/*@
  lemma void acc_add_overflow_all_same_chns<kt>(list<pair<kt, nat> > acc,
                                                list<pair<kt, nat> > orig,
                                                list<bucket<kt> > buckets,
                                                kt k, int dist)
  requires length(buckets) <= dist &*&
           true == multiset_eq(acc, cons(pair(k, nat_of_int(dist)), orig));
  ensures buckets_get_chns_rec_fp(acc, buckets) ==
          buckets_get_chns_rec_fp(cons(pair(k, nat_of_int(length(buckets))),
                                       orig),
                                  buckets);
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        switch(h) { case bucket(chains):
          list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
          list<pair<kt, nat> > orig_atb = acc_at_this_bucket(orig, h);
          multiset_eq_append_both(acc, cons(pair(k, nat_of_int(dist)), orig),
                                  chains);
          advance_acc_multiset_eq(atb, cons(pair(k, nat_of_int(dist)),
                                            orig_atb));
          multiset_eq_same_len(advance_acc(atb),
                               advance_acc(cons(pair(k, nat_of_int(dist)),
                                                orig_atb)));
          int prev_dist = dist - 1;
          assert nat_of_int(dist) == succ(nat_of_int(prev_dist));
          acc_add_overflow_all_same_chns(advance_acc(atb),
                                         advance_acc(orig_atb),
                                         t, k, dist - 1);
          assert nat_of_int(length(buckets)) == succ(nat_of_int(length(t)));
        }
    }
  }
  @*/


/*@
  lemma void put_overflow_chain_same_chns<kt>(list<pair<kt, nat> > acc,
                                              list<bucket<kt> > buckets,
                                              kt k, int start, int dist)
  requires length(buckets) <= start + dist &*&
           0 <= dist;
  ensures buckets_get_chns_rec_fp
            (acc, buckets_put_key_fp(buckets, k, start, dist)) ==
          buckets_get_chns_rec_fp
            (acc, buckets_put_key_fp(buckets, k, start,
                                     length(buckets) - start));
  {
    switch(buckets) {
      case nil:
      case cons(h,t):
        list<pair<kt, nat> > atb = acc_at_this_bucket(acc, h);
        if (start == 0) {
          switch(h) { case bucket(chains):
            list<pair<kt, nat> > new_atb =
              acc_at_this_bucket(acc, bucket_put_key_fp(h, k, dist));
            list<pair<kt, nat> > primary_atb =
              acc_at_this_bucket
                (acc, bucket_put_key_fp(h, k, length(buckets) - start));
            cons_in_the_middle_multiset_eq(acc, chains, pair(k, nat_of_int(dist)));
            cons_in_the_middle_multiset_eq
              (acc, chains, pair(k, nat_of_int(length(buckets) - start)));
            assert 0 < dist;
            int prev_dist = dist - 1;
            assert 0 < length(buckets) - start;
            int prev_lim_dist = length(buckets) - start - 1;
            assert nat_of_int(dist) == succ(nat_of_int(prev_dist));
            assert nat_of_int(length(buckets) - start) ==
                   succ(nat_of_int(prev_lim_dist));
            advance_acc_multiset_eq(new_atb, cons(pair(k, nat_of_int(dist)), atb));
            advance_acc_multiset_eq(primary_atb,
                                    cons(pair(k, nat_of_int(length(buckets) -
                                                            start)),
                                    atb));
            multiset_eq_same_len(advance_acc(new_atb),
                                 advance_acc(cons(pair(k, nat_of_int(dist)),
                                             atb)));
            multiset_eq_same_len(advance_acc(primary_atb),
                                 advance_acc
                                   (cons(pair(k, nat_of_int(length(buckets) -
                                                            start)),
                                         atb)));
            assert length(advance_acc(primary_atb)) ==
                   length(advance_acc(new_atb));
            acc_add_overflow_all_same_chns(advance_acc(new_atb), advance_acc(atb),
                                          t, k, dist - 1);
            acc_eq_get_chns_eq(advance_acc(primary_atb),
                               cons(pair(k, nat_of_int(length(t))),
                                    advance_acc(atb)),
                               t);
          }
        } else {
          put_overflow_chain_same_chns(advance_acc(atb), t, k, start - 1, dist);
        }
    }
  }
  @*/


/*@
  lemma void buckets_add_part_get_chns_inv<kt>(list<bucket<kt> > buckets,
                                               kt k, int start, int dist)
  requires length(buckets) < start + dist &*&
           0 <= start &*& start < length(buckets) &*&
           0 <= dist;
  ensures buckets_get_chns_fp(buckets_put_key_fp(buckets, k,
                                                 start, dist)) ==
          add_partial_chain_fp(start, dist,
                               buckets_get_chns_fp(buckets));
  {
    buckets_put_wraparound_eq_cons(nil, buckets, k, start, dist);
    assert true == multiset_eq
            (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
             cons(pair(k, nat_of_int(dist + start - length(buckets))),
                  get_wraparound(nil, buckets)));
    acc_eq_cons_get_chns_like_add_part_chn
      (get_wraparound(nil, buckets_put_key_fp(buckets, k, start, dist)),
       get_wraparound(nil, buckets),
       buckets_put_key_fp(buckets, k, start, dist),
       k, dist + start - length(buckets));
    put_overflow_chain_same_chns(get_wraparound(nil, buckets),
                                 buckets, k, start, dist);
    assert buckets_get_chns_rec_fp
             (get_wraparound(nil, buckets),
              buckets_put_key_fp(buckets, k, start, dist)) ==
           buckets_get_chns_rec_fp
             (get_wraparound(nil, buckets),
              buckets_put_key_fp(buckets, k, start,
                                 length(buckets) - start));
    buckets_add_part_get_chns_norm_rec(get_wraparound(nil, buckets),
                                       buckets,
                                       k, start,
                                       length(buckets) - start);
    assert buckets_get_chns_rec_fp
             (get_wraparound(nil, buckets),
              buckets_put_key_fp(buckets, k, start,
                                 length(buckets) - start)) ==
           add_partial_chain_rec_fp
             (buckets_get_chns_rec_fp(get_wraparound(nil, buckets), buckets),
              start, length(buckets) - start);
    buckets_keys_chns_same_len_rec(get_wraparound(nil, buckets), buckets);
    add_part_chain_rec_overflow(buckets_get_chns_rec_fp
                                  (get_wraparound(nil, buckets), buckets),
                                start, length(buckets) - start, dist);
    assert add_partial_chain_rec_fp
             (buckets_get_chns_rec_fp(get_wraparound(nil, buckets), buckets),
                                      start, length(buckets) - start) ==
           add_partial_chain_rec_fp
             (buckets_get_chns_rec_fp(get_wraparound(nil, buckets), buckets),
                                      start, dist);
  }//took 240m
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
      buckets_add_part_get_chns_lim(buckets, k, start);
    } else if (fin < start) {
      dist = fin + capacity - start;
      loop_bijection(fin - start + capacity, capacity);
      buckets_add_part_get_chns_inv(buckets, k, start, dist);
      loop_injection_n(fin + capacity, capacity, -1);
    } else {
      dist = fin - start;
      loop_injection_n(fin - start + capacity, capacity, -1);
      loop_bijection(fin - start, capacity);
      buckets_add_part_get_chns_norm(buckets, k, start, dist);
    }
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
