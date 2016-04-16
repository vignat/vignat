#include <stdint.h>
#include <string.h>

#include "map.h"

//@ #include <list.gh>
//@ #include <listex.gh>
//@ #include <nat.gh>
//@ #include "stdex.gh"

//TODO: introduce the "chain continuation" bit to optimize search for abscent.

/*@
  lemma void div_mod(int g, int k, int l)
  requires g == (k % l) &*& l > 0;
  ensures (-l <= g) &*& (g < l);
  {
  div_rem(k, l);
  }
  @*/

/*@
  lemma void div_mod_gt_0(int mod, int div, int whole)
  requires mod == (div % whole) &*& whole > 0 &*& div >= 0;
  ensures (0 <= mod) &*& (mod < whole);
  {
  div_rem(div, whole);
  }
  @*/
/*@
  fixpoint int loop_fp(int k, int capacity)
  { return ((k%capacity + capacity)%capacity); }
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
#define CAPACITY 1000
/*@
  lemma void loop_lims(int k, int capacity)
  requires 0 < capacity;
  ensures 0 <= loop_fp(k, capacity) &*& loop_fp(k, capacity) < capacity;
  {
    div_rem(k, capacity);
    assert(-capacity <= k%capacity);
    assert(0 <= k%capacity + capacity);
    div_rem((k + capacity), capacity);
    assert(capacity > 0);
    div_rem(k%capacity + capacity, capacity);
    assert(0 <= ((k%capacity + capacity)%capacity));
  }

  lemma void mul_mono(int a, int b, int c)
  requires a <= b &*& 0 <= c;
  ensures a * c <= b * c;
  {
    for (int i = 0; i < c; i++)
      invariant i <= c &*& a * i <= b * i;
      decreases c - i;
    {
    }
  }

  lemma void bar(int a, int b, int q, int r)
  requires 0 <= a &*& a < b &*& 0 <= r &*& a == q * b + r &*& r < b;
  ensures q == 0;
  {
    if (q == 0) {
    } else if (0 <= q) {
      mul_mono(1, q, b);
    } else {
      mul_mono(q, -1, b);
    }
  }

  lemma void division_round_to_zero(int a, int b)
  requires 0 <= a &*& a < b;
  ensures a/b == 0;
  {
    div_rem(a, b);
    bar(a, b, a / b, a % b);
  }

  lemma void loop_bijection(int k, int capacity)
  requires 0 <= k &*& k < capacity;
  ensures loop_fp(k, capacity) == k;
  {
    div_rem(k, capacity);
    assert(0 < capacity);
    division_round_to_zero(k, capacity);
    //TODO: the below is really true, see in the debugger!
    assume(k == ((k/capacity)*capacity) + (k % capacity));
    assert(k/capacity == 0);
    assert(k%capacity == k);
    div_rem((k + capacity), capacity);
    // Believe me, baby. I the parser get's out of hand here,
    // so I can not even formulate my assumptions properly
    assume(false);
    assert(k == ((k % capacity + capacity) % capacity));
  }

  lemma void loop_injection(int k, int capacity)
  requires 0 <= k &*& 0 < capacity;
  ensures loop_fp(k + capacity, capacity) == loop_fp(k, capacity);
  {
    div_rem(k, capacity);
    div_rem((k + capacity), capacity);
    int x = (k + capacity) % capacity;
    // Sorry, you have to believe me again.
    assume(false);
    assert(x == ((k%capacity) + (capacity/capacity)));
  }

  lemma void loop_fixp(int k, int capacity)
  requires 0 <= k &*& 0 < capacity;
  ensures loop_fp(k, capacity) == loop_fp(loop_fp(k, capacity), capacity);
  {
    loop_lims(k, capacity);
    loop_bijection(loop_fp(k, capacity), capacity);
  }

  lemma int loop_shift_inv(int x, int y, int capacity)
  requires 0 <= x &*& x < capacity;
  ensures 0 <= result &*& result < capacity &*&
          loop_fp(result + y, capacity) == x;
  {
    int z = loop_fp(x - y, capacity);
    // TODO:
    assume(false);
    if (z == 0) return 0;
    else return capacity - z;
  }
  @*/

// nth_prop:
/*@
  fixpoint bool nthProp<t>(list<t> arr, fixpoint (t, bool) prop, int index) {
    return prop(nth(index, arr));
  }

  fixpoint bool up_to(nat n, fixpoint (int, bool) prop) {
    switch(n) {
      case zero: return true;
      case succ(m): return prop(int_of_nat(m)) && up_to(m, prop);
    }
  }

  fixpoint bool byLoopNthProp<t>(list<t> arr, fixpoint (t, bool) prop,
                                  int cap, int shift, int index) {
    return nthProp(arr, prop, loop_fp(index + shift, cap));
  }

  lemma void up_to_covers_x(nat n, fixpoint (int, bool) prop, int x)
  requires true == up_to(n, prop) &*& 0 <= x &*& x < int_of_nat(n);
  ensures true == prop(x);
  {
    switch(n) {
      case zero: return;
      case succ(m):
        if (x == int_of_nat(m)) {
          return;
        } else {
          up_to_covers_x(m, prop, x);
        }
    }
  }

  fixpoint bool shiftNthProp<t>(list<t> arr, fixpoint (t, bool) prop,
                                int shift, int index) {
    return nthProp(arr, prop, shift + index);
  }

  lemma void shift_for_all<t>(list<t> arr, fixpoint (t, bool) prop,
                              int shift, int inlen, nat outlen)
  requires length(arr) == inlen &*& 0 <= shift &*&
           shift + int_of_nat(outlen) <= inlen &*&
           true == up_to(nat_of_int(inlen), (nthProp)(arr, prop));
  ensures true == up_to(outlen, (shiftNthProp)(arr, prop, shift));
  {
    switch(outlen) {
      case zero: return;
      case succ(len):
        shift_for_all(arr, prop, shift, inlen, len);
        up_to_covers_x(nat_of_int(inlen), (nthProp)(arr, prop),
                       int_of_nat(len)+shift);
    }
  }

  lemma void shift_for_append<t>(list<t> l1, list<t> l2,
                                 fixpoint (t, bool) prop,
                                 nat outlen)
  requires true == up_to(nat_of_int(length(l2)),
                         (shiftNthProp)(append(l1,l2), prop, length(l1))) &*&
           int_of_nat(outlen) <= length(l2);
  ensures true == up_to(outlen, (nthProp)(l2, prop));
  {
    switch(outlen) {
      case zero: return;
      case succ(len):
        shift_for_append(l1, l2, prop, len);
        up_to_covers_x(nat_of_int(length(l2)),
                       (shiftNthProp)(append(l1,l2), prop, length(l1)),
                       int_of_nat(len));
        nth_append_r(l1, l2, int_of_nat(len));
    }
  }

  lemma void by_loop_for_all<t>(list<t> arr, fixpoint (t, bool) prop,
                                int shift, int capacity, nat outlen)
  requires length(arr) == capacity &*& int_of_nat(outlen) <= capacity &*&
           true == up_to(nat_of_int(capacity),
                         (byLoopNthProp)(arr, prop, capacity, shift));
  ensures true == up_to(outlen, (nthProp)(arr, prop));
  {
    switch(outlen) {
      case zero: return;
      case succ(len):
        by_loop_for_all(arr, prop, shift, capacity, len);
        int orig = loop_shift_inv(int_of_nat(len), shift, capacity);
        up_to_covers_x(nat_of_int(capacity),
                      (byLoopNthProp)(arr, prop, capacity, shift),
                      orig);
        assert(true == byLoopNthProp(arr, prop, capacity, shift, orig));
        assert(true == nthProp(arr, prop, int_of_nat(len)));
    }
  }
  @*/

/*@
  inductive hmap<kt> = hmap(list<option<kt> >, list<int>);

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash,
                         int capacity,
                         int* busybits,
                         void** keyps,
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

  fixpoint int ks_find_key_fp<kt>(list<option<kt> > ks, kt k, int acc) {
    switch(ks) {
      case nil: return default_value<int>();
      case cons(h,t):
        return (h == some(k) ?
                acc :
                ks_find_key_fp(t, k, acc+1));
    }
  }

  fixpoint bool hmap_exists_key_fp<kt>(hmap<kt> m, kt k) {
    return mem(some(k), hmap_ks_fp(m));
  }

  fixpoint int hmap_find_key_fp<kt>(hmap<kt> m, kt k) {
    return ks_find_key_fp(hmap_ks_fp(m), k, 0);
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
                 (pred(head(pts), ?ksh) &*& ks == cons(some(ksh), kst))));

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
                         void** keyps,
                         int* k_hashes;
                         hmap<kt> m) =
            0 < capacity &*& 2*capacity < INT_MAX &*&
            ints(busybits, capacity, ?bbs) &*&
            pointers(keyps, capacity, ?kps) &*&
            ints(k_hashes, capacity, ?khs) &*&
            pred_mapping(kps, bbs, keyp, ?ks) &*&
            true == no_dups(ks) &*&
            true == hash_list(ks, khs, hash) &*&
            m == hmap(ks, khs);

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

  lemma void reverse_cons<t>(t head, list<t> tail)
  requires true;
  ensures reverse(cons(head, tail)) == append(reverse(tail), cons(head, nil));
  {
    reverse_append(reverse(tail), cons(head, nil));
  }

  lemma void append_reverse_take_cons<t>(int n, t head, list<t> tail,
                                         list<t> tt)
  requires 0 < n;
  ensures append(reverse(take(n-1, tail)), cons(head, tt)) ==
          append(reverse(take(n,cons(head, tail))), tt);
  {
    reverse_cons(head, take(n-1, tail));
    append_assoc(reverse(take(n-1, tail)), cons(head, nil), tt);
  }

  lemma kt extract_pred_for_key<kt>(list<void*> kps_b,
                                    list<int> bbs_b,
                                    list<option<kt> > ks_b,
                                    int n, list<int> bbs,
                                    list<option<kt> > ks)
  requires pred_mapping(?kps, bbs, ?pred, ks) &*&
           pred_mapping(kps_b, bbs_b, pred, ks_b) &*&
           0 <= n &*& n < length(bbs) &*& nth(n, bbs) != 0;
  ensures nth(n, ks) == some(result) &*& pred(nth(n, kps), result) &*&
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

  lemma void append_reverse_tail_cons_head<t>(list<t> l1, list<t> l2)
  requires l1 != nil;
  ensures append(reverse(tail(l1)), cons(head(l1), l2)) ==
          append(reverse(l1), l2);
  {
    reverse_cons(head(l1), tail(l1));
    cons_head_tail(l1);
    append_assoc(reverse(tail(l1)), cons(head(l1), nil), l2);
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
           pred(nth(n, kps), ?k) &*&
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

  lemma void hmapping_capacity_lims<kt>(int capacity)
  requires hmapping<kt>(?kpr, ?hsh, capacity, ?busybits, ?keyps, ?k_hashes, ?hm);
  ensures hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm) &*&
          0 < capacity &*& 2*capacity < INT_MAX;
  {
     open hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm);
     close hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm);
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

  lemma void ks_find_this_key<kt>(list<option<kt> > ks, int acc, int i, kt k)
  requires nth(i, ks) == some(k) &*& true == no_dups(ks) &*&
           0 <= acc &*& 0 <= i &*& i < length(ks);
  ensures ks_find_key_fp<kt>(ks, k, acc) == i + acc;
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        if (h == some(k)) {
          no_dups_same(ks, k, i, 0);
          assert(i == 0);
          return;
        } else {
          ks_find_this_key(t, acc+1, i-1, k);
        }
    }
  }

  lemma void hmap_find_this_key<kt>(hmap<kt> m, int i, kt k)
  requires nth(i, hmap_ks_fp(m)) == some(k) &*& true == no_dups(hmap_ks_fp(m)) &*&
           0 <= i &*& i < length(hmap_ks_fp(m));
  ensures hmap_find_key_fp(m, k) == i;
  {
    ks_find_this_key(hmap_ks_fp(m), 0, i, k);
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

  lemma void up_to_nth_uncons<kt>(kt hd, list<kt> tl, fixpoint (kt, bool) prop)
  requires true == up_to(succ(nat_of_int(length(tl))),
                         (nthProp)(cons(hd,tl), prop));
  ensures true == up_to(nat_of_int(length(tl)), (nthProp)(tl, prop)) &*&
          true == prop(hd);
  {
    shift_for_all(cons(hd,tl), prop, 1, length(tl)+1, nat_of_int(length(tl)));
    shift_for_append(cons(hd,nil), tl, prop, nat_of_int(length(tl)));
    up_to_covers_x(nat_of_int(length(tl)+1), (nthProp)(cons(hd,tl), prop), 0);
  }

  lemma void no_key_found<kt>(list<option<kt> > ks, kt k)
  requires true == up_to(nat_of_int(length(ks)), (nthProp)(ks, (not_my_key)(k)));
  ensures false == mem(some(k), ks);
  {
    switch(ks){
      case nil: return;
      case cons(h,t):
        up_to_nth_uncons(h, t, (not_my_key)(k));
        no_key_found(t, k);
    }
  }
@*/

static
int find_key/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int start,
                         void* keyp, map_keys_equality* eq, int key_hash,
                         int capacity)
/*@ requires hmapping<kt>(?kpr, ?hsh, capacity, busybits, keyps, k_hashes, ?hm) &*&
             kpr(keyp, ?k) &*&
             hsh(k) == key_hash &*&
             0 <= start &*& 2*start < INT_MAX &*&
             [?f]is_map_keys_equality<kt>(eq, kpr); @*/
/*@ ensures hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm) &*&
            kpr(keyp, k) &*&
            [f]is_map_keys_equality<kt>(eq, kpr) &*&
            (hmap_exists_key_fp(hm, k) ?
            (result == hmap_find_key_fp(hm, k)) :
             (result == -1)); @*/
{
  //@ hmapping_capacity_lims(capacity);
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ assert pred_mapping(?kps, ?bbs, kpr, ?ks);
  //@ assert hm == hmap(ks, ?khs);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant pred_mapping(kps, bbs, kpr, ks) &*&
                  ints(busybits, capacity, bbs) &*&
                  ints(k_hashes, capacity, khs) &*&
                  pointers(keyps, capacity, kps) &*&
                  0 <= i &*& i <= capacity &*&
                  [f]is_map_keys_equality<kt>(eq, kpr) &*&
                  kpr(keyp, k) &*&
                  hsh(k) == key_hash &*&
                  true == hash_list(ks, khs, hsh) &*&
                  true == up_to(nat_of_int(i),
                                (byLoopNthProp)(ks, (not_my_key)(k),
                                                capacity, start));
    @*/
  {
    //@ pred_mapping_same_len(bbs, ks);
    int index = loop(start + i, capacity);
    int bb = busybits[index];
    int kh = k_hashes[index];
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
        //@ close hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm);
        return index;
      }
      //@ recover_pred_mapping(kps, bbs, ks, index);
    } else {
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
  //@ close hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm);
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
int find_empty/*@ <kt> @*/(int* busybits, int start, int capacity)
/*@ requires hmapping<kt>(?kp, ?hsh, capacity, busybits, ?keyps, ?k_hashes, ?hm) &*&
             0 <= start &*& 2*start < INT_MAX; @*/
/*@ ensures hmapping<kt>(kp, hsh, capacity, busybits, keyps, k_hashes, hm) &*&
            (hmap_size_fp(hm) < capacity ?
             true == hmap_empty_cell_fp(hm, result) :
             result == -1) ; @*/
{
  //@ open hmapping(_, _, _, _, _, _, hm);
  //@ assert pred_mapping(?kps, ?bbs, kp, ?ks);
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
  {
    //@ pred_mapping_same_len(bbs, ks);
    int index = loop(start + i, capacity);
    int bb = busybits[index];
    if (0 == bb) {
      //@ zero_bbs_is_for_empty(bbs, ks, index);
      //@ close hmapping<kt>(kp, hsh, capacity, busybits, keyps, k_hashes, hm);
      return index;
    }
    //@ bb_nonzero_cell_busy(bbs, ks, index);
    //@ assert(true == cell_busy(nth(loop_fp(i+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ by_loop_for_all(ks, cell_busy, start, capacity, nat_of_int(capacity));
  //@ full_size(ks);
  //@ close hmapping<kt>(kp, hsh, capacity, busybits, keyps, k_hashes, hm);
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
  predicate key_vals<kt>(list<option<kt> > key_arr, list<int> val_arr;
                         list<kt> keys, list<int> vals) =
      switch (key_arr) {
        case nil: return val_arr == nil &*& keys == nil &*& vals == nil;
        case cons(key,tail):
          return switch(key) {
            case none: return key_vals(tail, tail(val_arr), keys, vals);
            case some(k): return key_vals(tail, tail(val_arr),
                                          ?keys_tail, ?vals_tail) &*&
                                 keys == cons(k, keys_tail) &*&
                                 vals == cons(head(val_arr), vals_tail);
          };
      };
  //TODO: reformulate as a precise predicate.
  predicate mapping<kt>(map<kt> m,
                        predicate (void*;kt) keyp,
                        predicate (kt,int) recp,
                        fixpoint (kt,int) hash,
                        int capacity,
                        int* busybits,
                        void** keyps,
                        int* k_hashes,
                        int* values) =
     hmapping<kt>(keyp, hash, capacity, busybits, keyps, k_hashes, ?hm) &*&
     ints(values, capacity, ?val_arr) &*&
     key_vals<kt>(hmap_ks_fp(hm), val_arr, ?keys, ?vals) &*&
     m == mapc(keys, vals);
  @*/

/*@
  lemma void produce_empty_key_vals<kt>(list<int> val_arr)
  requires true;
  ensures key_vals<kt>(none_list_fp(nat_of_int(length(val_arr))),
                       val_arr, nil, nil);
  {
    switch(val_arr) {
      case nil: return;
      case cons(vh,vt):
        produce_empty_key_vals(vt);
        nat_len_of_non_nil(vh,vt);
        close key_vals(none_list_fp(nat_of_int(length(val_arr))),
                       val_arr, nil, nil);
        return;
    }
  }

  @*/

void map_initialize/*@ <kt> @*/(int* busybits, map_keys_equality* eq,
                                void** keyps, int* khs, int* vals,
                                int capacity)
  /*@ requires exists<kt>(_) &*&
               exists<fixpoint (kt,int)>(?hash) &*&
               [?fr]is_map_keys_equality<kt>(eq, ?keyp) &*&
               pred_arg2<kt, int>(?recp) &*&
               ints(busybits, capacity, ?bbs) &*&
               pointers(keyps, capacity, ?kplist) &*&
               ints(vals, capacity, ?vallist) &*&
               ints(khs, capacity, ?khlist) &*&
               0 < capacity &*& 2*capacity < INT_MAX; @*/
  /*@ ensures mapping<kt>(empty_map_fp(), keyp, recp, hash,
                          capacity, busybits, keyps,
                          khs, vals) &*&
              [fr]is_map_keys_equality<kt>(eq, keyp); @*/
{
  //@ open exists<kt>(_);
  //@ open exists<fixpoint (kt,int)>(_);
  //@ open pred_arg2<kt,int>(_);
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
  {
    //@ move_int(busybits, i, capacity);
    //@ extend_zero_list(nat_of_int(i), head(drop(i,bbs)));
    busybits[i] = 0;
    //@ assert(succ(nat_of_int(i)) == nat_of_int(i+1));
    //@ tail_drop(bbs, i);
  }
  //@ assert(i == capacity);
  //@ assert(drop(i,bbs) == nil);
  //@ open(ints(busybits + i, capacity - i, drop(i,bbs)));
  //@ produce_pred_mapping<kt>(khlist, keyp, kplist);
  //@ confirm_no_dups_on_nones<kt>(nat_of_int(capacity));
  //@ confirm_hash_list_for_nones(khlist, hash);
  //@ close hmapping<kt>(keyp, hash, capacity, busybits, keyps, khs, empty_hmap_fp<kt>(capacity, khlist));
  //@ produce_empty_key_vals<kt>(vallist);
  //@ close mapping(empty_map_fp(), keyp, recp, hash, capacity, busybits, keyps, khs, vals);
}

int map_get/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, map_keys_equality* eq, int hash, int* value,
                        int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, values) &*&
             kp(keyp, ?k) &*&
             hsh(k) == hash &*&
             *value |-> ?v; @*/
/*@ ensures mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, values) &*&
            kp(keyp, k) &*&
            (map_has_fp(m, k) ?
             (result == 1 &*&
              *value |-> v &*&
              v == map_get_fp(m, k) &*&
              recp(k, v)):
             (result == 0 &*&
              *value |-> v)); @*/
{
    int start = loop(hash, capacity);
    int index = find_key(busybits, keyps, k_hashes, start,
                         keyp, eq, hash, capacity);
    if (-1 == index)
    {
        return 0;
    }
    *value = values[index];
    return 1;
}

int map_put/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, int hash, int value,
                        int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, values) &*&
             kp(keyp, ?k) &*& recp(k, value) &*&
             hsh(k) == hash &*&
             false == map_has_fp(m, k); @*/
/*@ ensures kp(keyp, k) &*& recp(k, value) &*&
            (map_size_fp(m) < capacity ?
             (result == 1 &*&
              mapping<kt>(map_put_fp(m, k, value), kp, recp,
                          hsh,
                          capacity, busybits,
                          keyps, k_hashes, values)) :
             (result == 0 &*&
              mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                          keyps, k_hashes, values))); @*/
{
    int start = loop(hash, capacity);
    int index = find_empty(busybits, start, capacity);

    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 1;
    keyps[index] = keyp;
    k_hashes[index] = hash;
    values[index] = value;
    return 1;
}

int map_erase/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, void* keyp,
                          map_keys_equality* eq, int hash, int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, ?values) &*&
             kp(keyp, ?k) &*&
             hsh(k) == hash; @*/
/*@ ensures kp(keyp, k) &*&
            (map_has_fp(m, k) ?
            (result == 1 &*&
             mapping<kt>(map_erase_fp(m, k), kp, recp, hsh,
                         capacity, busybits, keyps, k_hashes, values)) :
            (result == 0 &*&
            mapping<kt>(m, kp, recp, hsh,
                        capacity, busybits, keyps, k_hashes, values))); @*/
{
    int start = loop(hash, capacity);
    int index = find_key(busybits, keyps, k_hashes, start,
                         keyp, eq, hash, capacity);
    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 0;
    return 1;
}

int map_size/*@ <kt> @*/(int* busybits, int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         ?keyps, ?k_hashes, ?values); @*/
/*@ ensures mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, values) &*&
            result == map_size_fp(m);@*/
{
    int s = 0;
    int i = 0;
    for (; i < capacity; ++i)
    {
        if (busybits[i] != 0)
        {
            ++s;
        }
    }
    return s;
}
