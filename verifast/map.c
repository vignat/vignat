//@ #include <list.gh>
//@ #include <listex.gh>

#define CAPACITY 1000000

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
  fixpoint int loop_l(int k) { return ((k%CAPACITY + CAPACITY)%CAPACITY); }
  @*/

int loop (int k)
//@ requires true;
//@ ensures 0 <= result &*& result < CAPACITY &*& result==loop_l(k);
{
    int g = k%CAPACITY;
    //@ div_mod(g, k, CAPACITY);
    int res = (g + CAPACITY)%CAPACITY;
    //@ div_mod_gt_0(res, g + CAPACITY, CAPACITY);
    return res;
}

/*@
  lemma void loop_lims(int k)
  requires true;
  ensures 0 <= loop_l(k) &*& loop_l(k) < CAPACITY;
  {
    div_rem(k, CAPACITY);
    assert(-CAPACITY <= k%CAPACITY);
    assert(0 <= k%CAPACITY + CAPACITY);
    div_rem((k + CAPACITY), CAPACITY);
    assert(CAPACITY > 0);
    div_rem(k%CAPACITY + CAPACITY, CAPACITY);
    assert(0 <= ((k%CAPACITY + CAPACITY)%CAPACITY));
  }

  lemma void loop_bijection(int k)
  requires 0 <= k &*& k < CAPACITY;
  ensures loop_l(k) == k;
  {
    div_rem(k, CAPACITY);
    assert(k%CAPACITY == k);
    div_rem((k + CAPACITY), CAPACITY);
    assert(k == ((k % CAPACITY + CAPACITY) % CAPACITY));
  }
  
  lemma void loop_injection(int k)
  requires 0 <= k;
  ensures loop_l(k + CAPACITY) == loop_l(k);
  {
    div_rem(k, CAPACITY);
    div_rem((k + CAPACITY), CAPACITY);
    int x = (k + CAPACITY) % CAPACITY;
    assert(x == ((k)%CAPACITY));
  }
  
  lemma void loop_fixp(int k)
  requires 0 <= k;
  ensures loop_l(k) == loop_l(loop_l(k));
  {
    loop_lims(k);
    loop_bijection(loop_l(k));
  }
  
  fixpoint bool loopcontainedin(list<int> xs, int start, int x) { return contains(xs, loop_l((int)(start + x))); }
  fixpoint bool byloop(list<int> ys, list<int> xs, int start) { return forall(ys, (loopcontainedin)(xs, start)); }
  
  lemma void forallLCIappend(list<int> xs, list<int> ys, int y, int start)
  requires true == forall(xs, (loopcontainedin)(ys, start));
  ensures true == forall(xs, (loopcontainedin)(cons(y, ys), start));
  {
    switch(xs) {
      case nil: return;
      case cons(h, t):
        assert(true == loopcontainedin(ys, start, h));
        assert(true == loopcontainedin(cons(y, ys), start, h));
        forallLCIappend(t, ys, y, start);
        return;
    }
  }

  @*/

/*@
      predicate nat_seq(list<int> lst) =
        lst == nil ? true :
          head(lst) == 0 ? tail(lst) == nil :
          tail(lst)!= nil &*& head(lst) == 1 + head(tail(lst)) &*& nat_seq(tail(lst));
          
      lemma void nat_seq_head_len(list<int> lst)
      requires nat_seq(lst);
      ensures nat_seq(lst) &*& (lst == nil || (head(lst) + 1 == length(lst)));
      {
        switch (lst) {
          case nil:
            return;
          case cons(h, t):
            open nat_seq(lst);
            if (head(lst) == 0)
            {
              assert(tail(lst) == nil);
              assert(length(lst) == 1);
            }
            else
            {
              nat_seq_head_len(t);
              assert(t!=nil);
              assert(head(lst) == 1 + head(tail(lst)));
              assert(head(tail(lst)) + 1 == length(tail(lst)));
              assert(length(lst) == 1 + length(tail(lst)));
              assert(head(lst) + 1 == length(lst));
            }
            close nat_seq(lst);
          };
      }
      
      lemma void nat_seq_append_len(list<int> seq)
      requires nat_seq(seq);
      ensures nat_seq(cons(length(seq), seq));
      {
        switch(seq) {
          case nil:
            open nat_seq(seq);
            assert(length(seq) == 0);
            close nat_seq(cons(length(seq), seq));
            return;
          case cons(h, t):
            nat_seq_head_len(seq);
            close nat_seq(cons(length(seq), seq));
            return;
        }
      }

  @*/

/*@


lemma void nat_seq_cont(list<int> seq, int x)
requires nat_seq(seq) &*& 0 <= x &*& x < (length(seq));
ensures nat_seq(seq) &*& true == contains(seq, x);
{
  switch(seq) {
    case nil: return;
    case cons(h, t):
      nat_seq_head_len(seq);
      open nat_seq(seq);
      if (h == 0)
      {
        assert(length(seq) == 1);
        assert(x == 0);
        assert(x == head(seq));
      }
      else
      {
        if (h == x) {}
        else
        {
          assert(x < h + 1);
          assert(x != h);
          assert(x < h);
          assert(x < length(t));
          nat_seq_cont(t, x);
          assert(true == contains(t, x));
        }
      }
      close nat_seq(seq);
      assert(true == contains(seq, x));
      return;
  }   
}

lemma void nat_seq_ge_0(list<int> seq)
requires nat_seq(seq) &*& seq != nil;
ensures nat_seq(seq) &*& head(seq) >= 0 &*& seq != nil;
{
  switch(seq) {
    case nil: return;
    case cons(h, t):
      length_nonnegative(t);
      nat_seq_head_len(seq);
      return;
  }
}

lemma list<int> replicate_nat_seq(list<int> seq)
requires nat_seq(seq);
ensures nat_seq(seq) &*& nat_seq(result) &*& (seq == nil ? result == nil : result != nil &*& head(seq) == head(result)) &*&
        length(result) == length(seq);
{
  switch(seq) {
    case nil:
      close nat_seq(nil);
      return nil;
    case cons(h, t):
      open nat_seq(seq);
      list<int> rt = nil;
      if (h == 0) {
        rt = cons(h, nil);
        close nat_seq(rt);
      }
      else {
        rt = replicate_nat_seq(t);
        rt = cons(h, rt);
        close nat_seq(rt);
      }
      close nat_seq(seq);
      return rt;
  }
}

lemma void destroy_nat_seq(list<int> nseq)
requires nat_seq(nseq);
ensures true;
{
  switch(nseq) {
    case nil: open nat_seq(nseq); return;
    case cons(h, t):
      open nat_seq(nseq);
      if (h != 0) destroy_nat_seq(t);
      return;
  }
}

@*/

/*@
  inductive busy_key = bkpair(int, int);
  
  fixpoint int bk_key(busy_key bk) {
    switch(bk) {
      case bkpair(bb, key): return key;
    }
  }
  
  fixpoint int bk_busybit(busy_key bk) {
    switch(bk) {
      case bkpair(bb, key): return bb;
    }
  }

  predicate bkeys(list<busy_key> bks, list<int> bbs, list<int> ks) =
    switch(bks) {
      case nil: return bbs == nil &*& ks == nil;
      case cons(bkh, bkt):
        return bbs != nil &*& ks != nil &*&
               bkh == bkpair(head(bbs), head(ks)) &*&
               bkeys(bkt, tail(bbs), tail(ks));
    };
    
  fixpoint bool has_key(list<busy_key> bks, int key) {
    switch(bks) {
      case nil: return false;
      case cons(h, t):
        return (bk_busybit(h) != 0 && bk_key(h) == key) || has_key(t, key);
    }
  }
  
  fixpoint bool not_a_valid_key(int key, busy_key bk) {
    return bk_key(bk) != key || bk_busybit(bk) == 0;
  }
  
  lemma void length_0_nil<T>(list<T> lst)
  requires length(lst) == 0;
  ensures lst == nil;
  {
    switch (lst) {
      case nil: return;
      case cons(h, t):
        assert(length(lst) > length(t));
        assert(length(t) == 0);
        assert(length(lst) > 0);
        assert(length(lst) == 0);
        return;
    }
  }

  
  lemma void nth_0_head(list<int> lst)
  requires lst != nil;
  ensures nth(0, lst) == head(lst);
  {
    switch(lst) {
      case nil: return;
      case cons(h, t): return;
    }
  }
  
  lemma void nth_cons<T>(int n, list<T> lst, T head)
  requires n > 0;
  ensures nth(n-1, lst) == nth(n, cons(head, lst));
  {
    switch(lst) {
      case nil: return;
      case cons(h, t): return;
    }
  }
  
  lemma void nth_len_append_cons<T>(list<T> lst, T x)
  requires true;
  ensures nth(length(lst), append(lst, cons(x, nil))) == x;
  {
    switch(lst) {
      case nil: return;
      case cons(h, t):
        nth_len_append_cons(t, x);
        return;
    }
  }
  
  lemma void nth_less_append_cons<T>(int n, list<T> lst, T x)
  requires 0 <= n &*& n < length(lst);
  ensures nth(n, append(lst, cons(x, nil))) == nth(n, lst);
  {
    switch(lst) {
      case nil: return;
      case cons(h, t):
        if (n == 0) {
          assert(h == nth(n, lst));
          assert(h == nth(n, append(lst, cons(x, nil))));
          return;
        } else {
          nth_less_append_cons(n - 1, t, x);
          return;
        }
    }
  }
  
  lemma void append_take_cons<T>(list<T> lst)
  requires lst != nil;
  ensures lst == append(take(length(lst) - 1, lst), cons(nth(length(lst) - 1, lst), nil));
  {
    switch(lst) {
      case nil: return;
      case cons(h, t):
        if (t == nil) {
          assert(length(lst) == 1);
          assert(take(length(lst) - 1, lst) == nil);
          assert(cons(nth(length(lst) - 1, lst), nil) == lst);
          assert(append(nil, lst) == lst);
          return;
        } else {
          append_take_cons(t);
          assert(take(length(lst) - 1, lst) == cons(h, take(length(t) - 1, t)));
          assert(nth(length(lst) - 1, lst) == nth(length(t) - 1, t));
          assert(append(take(length(lst) - 1, lst), cons(nth(length(lst) - 1, lst), nil)) ==
                 cons(h, append(take(length(t) - 1, t), cons(nth(length(t) - 1, t), nil))));
          return;
        }
    }
  }


  lemma void cons_take_take_cons<T>(T head, list<T> tail, int n)
  requires 0 <= n;
  ensures cons(head, take(n, tail)) == take(n + 1, cons(head, tail));
  {
    switch(tail) {
      case nil: return;
      case cons(h, t):
        return;
    }
  }

  
  lemma void cons_head_tail<T>(list<T> lst)
  requires lst != nil;
  ensures lst == cons(head(lst), tail(lst));
  {
    switch(lst){
      case nil: return;
      case cons(h, t): return;
    }
  }
  
  lemma void length_tail<T>(list<T> lst)
  requires lst != nil;
  ensures length(lst) == 1 + length(tail(lst));
  {
    switch(lst) {
      case nil: return;
      case cons(h,t): return;
    }
  }
  
  lemma void nth_bbs_keys_bkeys(int n, list<int> bbs, list<int> ks, list<busy_key> bks)
  requires bkeys(bks, bbs, ks) &*& 0 <= n &*& n < length(bks);
  ensures bkeys(bks, bbs, ks) &*& bk_key(nth(n, bks)) == nth(n, ks) &*& bk_busybit(nth(n, bks)) == nth(n, bbs);
  {
    open bkeys(bks, bbs, ks);
    switch(bks) {
      case nil:
        break;
      case cons(h, t):
        assert(ks != nil);
        assert(bbs != nil);
        if (n == 0) {
          nth_0_head(ks);
          nth_0_head(bbs);
          assert(nth(n, ks) == head(ks));
          assert(nth(n, bbs) == head(bbs));
          assert(h == bkpair(head(bbs), head(ks)));
        } else {
          nth_bbs_keys_bkeys(n - 1, tail(bbs), tail(ks), t);
          nth_cons(n, tail(bbs), head(bbs));
          nth_cons(n, tail(ks), head(ks));
          nth_cons(n, t, h);
          cons_head_tail(ks);
          cons_head_tail(bbs);
        }
        break;
    }
    close bkeys(bks, bbs, ks);
  }
  
  lemma void bkeys_len_eq(list<busy_key> bks, list<int> bbs, list<int> ks)
  requires bkeys(bks, bbs, ks);
  ensures bkeys(bks, bbs, ks) &*& length(bks) == length(bbs) &*& length(bks) == length(ks);
  {
    open bkeys(bks, bbs, ks);
    switch(bks) {
      case nil: break;
      case cons(h, t):
        assert(bbs != nil);
        assert(ks != nil);
        bkeys_len_eq(t, tail(bbs), tail(ks));
        assert(length(bks) == length(t) + 1);
        length_tail(bbs);
        length_tail(ks);
        assert(length(bbs) == length(tail(bbs)) + 1);
        assert(length(ks) == length(tail(ks)) + 1);
        break;
    }
    close bkeys(bks, bbs, ks);
  }
  
  lemma void does_have_key(int i, int key, list<busy_key> bks)
  requires 0 <= i &*& i < length(bks) &*& bk_key(nth(i, bks)) == key &*& bk_busybit(nth(i, bks)) != 0;
  ensures true == has_key(bks, key);
  {
    switch(bks) {
      case nil: return;
      case cons(h, t):
        if (i == 0) {
        } else {
          does_have_key(i - 1, key, t);
        }
        assert(true == has_key(bks, key));
        return;
    }
  }
  
  lemma void not_a_valid_key_cond(list<busy_key> bks, list<int> bbs, list<int> ks, int n, int key)
  requires bkeys(bks, bbs, ks) &*& 0 <= n &*& n < length(bks) &*& (nth(n, bbs) == 0 || nth(n, ks) != key);
  ensures bkeys(bks, bbs, ks) &*& true == nthProp(bks, (not_a_valid_key)(key), n);
  {
    nth_bbs_keys_bkeys(n, bbs, ks, bks);
  }
  @*/

/*@

fixpoint bool nthProp<T> (list<T> arr, fixpoint (T, bool) prop, int index) {
  return prop(nth(index, arr));
}

lemma void loopedProp<T>(list<int> olist, list<int> indices, list<int> ilist, list<T> arr, int start, fixpoint (T, bool) prop)
requires nat_seq(olist) &*& nat_seq(ilist) &*& true == forall(indices, (nthProp)(arr, prop)) &*& true == byloop(ilist, indices, start)
     &*& (length(ilist) == CAPACITY) &*& (length(olist) <= CAPACITY) &*& 0 <= start &*& start < CAPACITY;
ensures nat_seq(ilist) &*& nat_seq(olist) &*& true == forall(olist, (nthProp)(arr, prop));
{
  switch(olist) {
    case nil: break;
    case cons(h, t):
      nat_seq_ge_0(olist);
      nat_seq_head_len(olist);
      open nat_seq(olist);
      if (h == 0)
      {
        loop_injection(0);
        assert(h == 0);
        int x = h + (CAPACITY - start);
        if (x == CAPACITY) x = 0;
        assert(loop_l(start + x) == loop_l(h));
        loop_bijection(0);
        assert(loop_l(start + x) == h);
        assert(x < CAPACITY);
        nat_seq_cont(ilist, x);
        assert(true == contains(ilist, x));
        forall_mem(x, ilist, (loopcontainedin)(indices, start));
        assert(true == contains(indices, loop_l(start + x)));
        assert(true == mem(h, indices));
        forall_mem(h, indices, (nthProp)(arr, prop));
        assert(true == nthProp(arr, prop, h));
        assert(true == forall(olist, (nthProp)(arr, prop)));
      }
      else
      {
        assert(0 < h);
        assert(h < CAPACITY);
        int x = h + (CAPACITY - start);
        if (x >= CAPACITY) x = x - CAPACITY;
        loop_injection(h);
        assert(loop_l(start+x) == loop_l(h));
        loop_bijection(h);
        assert(loop_l(h) == h);
        loopedProp(t, indices, ilist, arr, start, prop);
        assert(true == forall(t, (nthProp)(arr, prop)));
        nat_seq_cont(ilist, x);
        forall_mem(x, ilist, (loopcontainedin)(indices, start));
        assert(true == mem(h, indices));
        forall_mem(h, indices, (nthProp)(arr, prop));
        assert(true == nthProp(arr, prop, h));
        assert(true == forall(olist, (nthProp)(arr, prop)));
      }
      close nat_seq(olist);
  }
}

fixpoint bool nthProp_or_outrange<T>(list<T> arr, fixpoint (T, bool) prop, int n) {
  return n < 0 || length(arr) <= n || nthProp(arr, prop, n);
}

lemma void forall_nthProp2nthProp_or_outrange<T>(list<int> seq, list<T> arr, fixpoint (T, bool) prop)
requires true == forall(seq, (nthProp)(arr, prop));
ensures true == forall(seq, (nthProp_or_outrange)(arr, prop));
{
  switch(seq) {
    case nil: return;
    case cons(h, t):
      assert(true == nthProp(arr, prop, h));
      assert(true == nthProp_or_outrange(arr, prop, h));
      forall_nthProp2nthProp_or_outrange(t, arr, prop);
      return;
  }
}

lemma void nat_seq_nthProp_or_outrange2nthProp<T>(list<int> nseq, list<T> arr, fixpoint (T, bool) prop)
requires nat_seq(nseq) &*& true == forall(nseq, (nthProp_or_outrange)(arr, prop)) &*& length(nseq) <= length(arr);
ensures nat_seq(nseq) &*& true == forall(nseq, (nthProp)(arr, prop));
{
  switch(nseq) {
    case nil: return;
    case cons(h, t):
      nat_seq_ge_0(nseq);
      assert(0 <= h);
      nat_seq_head_len(nseq);
      assert(h < length(arr));
      assert(true == nthProp_or_outrange(arr, prop, h));
      assert(true == nthProp(arr, prop, h));
      open nat_seq(nseq);
      if (h == 0) {
        assert(t == nil);
      } else {
        nat_seq_nthProp_or_outrange2nthProp(t, arr, prop);
      }
      close nat_seq(nseq);
  }
}


lemma void nat_take_subarr_nthProp_or_outrange<T>(list<int> nseq, list<T> arr, fixpoint (T, bool) prop)
requires nat_seq(nseq) &*& true == forall(nseq, (nthProp_or_outrange)(arr, prop)) &*& length(arr) > 0;
ensures nat_seq(nseq) &*& true == forall(nseq, (nthProp_or_outrange)(take(length(arr) - 1, arr), prop));
{
  switch(nseq) {
    case nil: return;
    case cons(h, t):
      nat_seq_ge_0(nseq);
      open nat_seq(nseq);
      if (h == 0) {
        assert(t == nil);
        if (length(arr) == 1) {
          assert(take(length(arr) - 1, arr) == nil);
          assert(true == nthProp_or_outrange(take(length(arr) -1, arr), prop, h));
        } else {
          assert(length(arr) - 1 > 0);
          assert(nth(h, take(length(arr) -1, arr)) == nth(h, arr));
          assert(true == nthProp_or_outrange(take(length(arr) - 1, arr), prop, h));
        }
      } else {
        if (h < length(arr) - 1) {
          assert(nth(h, take(length(arr) - 1, arr)) == nth(h, arr));
        } else {
          assert(length(take(length(arr) - 1, arr)) <= h);
        }
        assert(true == nthProp_or_outrange(take(length(arr) - 1, arr), prop, h));
        nat_take_subarr_nthProp_or_outrange(t, arr, prop);
      }
      close nat_seq(nseq);
      return;
  }
}

lemma void nthProp_or_outrange_on_empty<T>(list<int> nseq, list<T> arr, fixpoint (T, bool) prop)
requires length(arr) == 0;
ensures true == forall(nseq, (nthProp_or_outrange)(arr, prop));
{
  switch(nseq) {
    case nil: return;
    case cons(h, t):
      assert(0 < h || h <= length(arr));
      assert(true == nthProp_or_outrange(arr, prop, h));
      nthProp_or_outrange_on_empty(t, arr, prop);
      return;
  }
}

lemma void nthProp_or_outrange_append1<T>(list<int> seq, list<T> arr, T x, fixpoint (T, bool) prop)
requires true == forall(seq, (nthProp_or_outrange)(arr, prop)) &*& true == prop(x);
ensures true == forall(seq, (nthProp_or_outrange)(append(arr, cons(x, nil)), prop));
{
  switch(seq) {
    case nil: return;
    case cons(h, t):
      nthProp_or_outrange_append1(t, arr, x, prop);
      if (h < 0) return;
      else if (h > length(arr)) return;
      else if (h == length(arr)) {
        nth_len_append_cons(arr, x);
        assert(nth(h, append(arr, cons(x, nil))) == x);
        return;
      } else {
        assert(true == prop(nth(h, arr)));
        nth_less_append_cons(h, arr, x);
        assert(nth(h, append(arr, cons(x, nil))) == nth(h, arr));
        return;
      }
  }
}

lemma void nat_subarr_nthProp_or_outrange<T>(list<int> nseq, list<T> arr, T arrhead, fixpoint (T, bool) prop)
requires nat_seq(nseq) &*& true == forall(nseq, (nthProp_or_outrange)(cons(arrhead, arr), prop)) &*& length(arr) < length(nseq);
ensures nat_seq(nseq) &*& true == forall(nseq, (nthProp_or_outrange)(arr, prop));
{
  switch(nseq) {
    case nil: return;
    case cons(h, t):
      nat_seq_head_len(nseq);
      open nat_seq(nseq);
      if (h == 0) {
        assert(length(nseq) == 1);
        assert(length(arr) == 0);
        length_0_nil(arr);
        assert(arr == nil);
      } else {
        assert(true == forall(t, (nthProp_or_outrange)(cons(arrhead, arr), prop)));
        nat_take_subarr_nthProp_or_outrange(t, cons(arrhead, arr), prop);
        assert(length(arr) == length(cons(arrhead, arr)) - 1);
        int ll = length(arr);
        length_nonnegative(arr);
        if (ll == 0) {
          nthProp_or_outrange_on_empty(nseq, arr, prop);
        } else {
          cons_take_take_cons(arrhead, arr, ll - 1);
          assert(cons(arrhead, take(ll - 1, arr)) == take(ll, cons(arrhead, arr)));
          assert(cons(arrhead, take(length(arr) - 1, arr)) == take(length(cons(arrhead, arr)) - 1, cons(arrhead, arr)));
          nat_subarr_nthProp_or_outrange(t, take(length(arr) - 1, arr), arrhead, prop);
          assert(true == forall(t, (nthProp_or_outrange)(take(length(arr) - 1, arr), prop)));
          assert(true == forall(t, (nthProp_or_outrange)(cons(arrhead, arr), prop)));
          
          close nat_seq(nseq);
          nat_seq_cont(nseq, ll);
          open nat_seq(nseq);
          forall_mem(ll, nseq, (nthProp_or_outrange)(cons(arrhead, arr), prop));
          assert(true == nthProp_or_outrange(cons(arrhead, arr), prop, ll));
          assert(true == nthProp_or_outrange(arr, prop, ll - 1));
          
          nthProp_or_outrange_append1(t, take(ll - 1, arr), nth(ll - 1, arr), prop);
          assert(true == forall(t, (nthProp_or_outrange)(append(take(ll - 1, arr), cons(nth(ll - 1, arr), nil)), prop)));
          append_take_cons(arr);
          assert(arr == append(take(ll - 1, arr), cons(nth(ll - 1, arr), nil)));
          
          assert(true == forall(t, (nthProp_or_outrange)(arr, prop)));
          assert(h == length(nseq) - 1);
          assert(length(arr) <= h);
          assert(true == nthProp_or_outrange(arr, prop, h));
        }
      }
      close nat_seq(nseq);
      return;
  }
}


lemma void nat_subseq_prop_subarr<T>(list<int> nseq, int shead, list<T> arr, T arrhead, fixpoint (T, bool) prop)
requires nat_seq(cons(shead, nseq)) &*& true == forall(cons(shead, nseq), (nthProp)(cons(arrhead, arr), prop)) &*& length(nseq) == length(arr);
ensures nat_seq(cons(shead, nseq)) &*& true == forall(nseq, (nthProp)(arr, prop));
{
  assert(true == forall(cons(shead, nseq), (nthProp)(cons(arrhead, arr), prop)));
  forall_nthProp2nthProp_or_outrange(cons(shead, nseq), cons(arrhead, arr), prop);
  assert(true == forall(cons(shead, nseq), (nthProp_or_outrange)(cons(arrhead, arr), prop)));
  nat_subarr_nthProp_or_outrange(cons(shead, nseq), arr, arrhead, prop);
  assert(true == forall(nseq, (nthProp_or_outrange)(arr, prop)));
  open nat_seq(cons(shead, nseq));
  if (shead == 0) {
    assert(nseq == nil);
  } else {
    nat_seq_nthProp_or_outrange2nthProp(nseq, arr, prop);
  }
  close nat_seq(cons(shead, nseq));
  assert(true == forall(nseq, (nthProp)(arr, prop)));
}

lemma void nat_seq_forall<T>(list<int> nseq, list<T> arr, fixpoint (T, bool) prop)
requires nat_seq(nseq) &*& true == forall(nseq, (nthProp)(arr, prop)) &*& length(nseq) == length(arr);
ensures nat_seq(nseq) &*& true == forall(arr, prop);
{
  switch(nseq) {
    case nil:
      assert(length(arr) == 0);
      switch(arr) {
        case nil:
          return;
        case cons(ah, at):
          length_positive(at);
          assert(length(arr) == length(at) + 1);
          assert(length(arr) > 0);
          return;
      }
    case cons(h, t) :
      switch(arr) {
        case nil:
          return;
        case cons(ah, at):
          nat_seq_cont(nseq, 0);
          forall_mem(0, nseq, (nthProp)(arr, prop));
          assert(true == nthProp(arr, prop, 0));
          assert(true == prop(nth(0, arr)));
          assert(ah == nth(0, arr));
          nat_subseq_prop_subarr(t, h, at, ah, prop);
          assert(true == forall(t, (nthProp)(arr, prop)));
          open nat_seq(nseq);
          if (h == 0) {
            assert(t == nil);
            assert(length(arr) == 1);
            assert(length(at) == 0);
            length_0_nil(at);
            assert(at == nil);
          } else {
            nat_seq_forall(t, at, prop);
          }
          assert(true == forall(at, prop));
          close nat_seq(nseq);
          return;
      }
  }
}


lemma void forall_no_valid_key_has_no_key(list<busy_key> bks, int key)
requires true == forall(bks, (not_a_valid_key)(key));
ensures false == has_key(bks, key);
{
  switch(bks) {
    case nil: return;
    case cons(h, t):
      forall_no_valid_key_has_no_key(t, key);
      return;
  }
}

@*/

int find_key(int* busybits, int* keys, int start, int key)
     //@ requires 0 <= start &*& start < CAPACITY &*& ints(busybits, CAPACITY, ?bbs) &*& ints(keys, CAPACITY, ?ks) &*& bkeys(?bks, bbs, ks);
     //@ ensures ints(busybits, CAPACITY, bbs) &*& ints(keys, CAPACITY, ks) &*& bkeys(bks, bbs, ks) &*& \
         (has_key(bks, key) ? bk_key(nth(result, bks)) == key &*& bk_busybit(nth(result, bks)) != 0 : result == -1);
{
  //@ bkeys_len_eq(bks, bbs, ks);
  //@ list<int> indices = nil;
  //@ list<int> ilist = nil;
  //@ close nat_seq(ilist);
  for (int i = 0; i < CAPACITY; ++i)
  /*@
    invariant ints(busybits, CAPACITY, bbs) &*& ints(keys, CAPACITY, ks) &*& bkeys(bks, bbs, ks) &*&
              0 <= i &*& i <= CAPACITY &*& true == byloop(ilist, indices, start) &*& nat_seq(ilist) &*&
              length(bks) == CAPACITY &*&
              i == length(ilist) &*& true == forall(indices, (nthProp)(bks, (not_a_valid_key)(key)));
  @*/
  {
    int index = loop(start + i);
    int bb = busybits[index];
    int k = keys[index];
    if (bb != 0 && k == key) {
      //@ loop_lims(start + i);
      //@ nth_bbs_keys_bkeys(index, bbs, ks, bks);
      //@ destroy_nat_seq(ilist);
      //@ does_have_key(index, key, bks);
      return index;
    }
    //@ not_a_valid_key_cond(bks, bbs, ks, index, key);
    //@ forallLCIappend(ilist, indices, index, start);
    //@ indices = cons(index, indices);
    //@ assert(true == forall(ilist, (loopcontainedin)(indices, start)));
    //@ assert(true == byloop(ilist, indices, start));
    //@ nat_seq_append_len(ilist);
    //@ ilist = cons(i, ilist);
  }
  //@ list<int> olist = replicate_nat_seq(ilist);
  //@ loopedProp(olist, indices, ilist, bks, start, (not_a_valid_key)(key));
  //@ nat_seq_forall(olist, bks, (not_a_valid_key)(key));
  //@ forall_no_valid_key_has_no_key(bks, key);
  //@ destroy_nat_seq(ilist);
  //@ destroy_nat_seq(olist);
  return -1;
}

/*@

fixpoint bool busy(int x) { return x != 0; }

lemma void allbusy_no_free(list<int> bbs)
requires true == forall(bbs, busy);
ensures false == contains(bbs, 0);
{
  switch(bbs) {
    case nil: return;
    case cons(h, t):
      allbusy_no_free(t);
      return;
  }
}

@*/

int find_empty (int* busybits, int start)
    //@ requires 0 <= start &*& start < CAPACITY &*& ints(busybits, CAPACITY, ?bbs);
    //@ ensures ints(busybits, CAPACITY, bbs) &*& (contains(bbs, 0) ? nth(result, bbs) == 0 : result == -1);
  {
    //@ list<int> indices = nil;
    //@ list<int> ilist = nil;
    //@ close nat_seq(ilist);
    for (int i = 0; i < CAPACITY; ++i)
    /*@
     invariant ints(busybits, CAPACITY, bbs) &*& 0 <= i &*& i <= CAPACITY &*&
               true == forall(indices, (nthProp)(bbs, busy)) &*& true == byloop(ilist, indices, start) &*&
               nat_seq(ilist) &*& i == length(ilist);
     @*/
    {
        int index = loop(start + i);
        int bb = busybits[index];
        if (0 == bb) {
            //@ assert(busybits[index] == 0);
            //@ assert(nth(index, bbs) == 0);
            //@ destroy_nat_seq(ilist);
            return index;
        }
        //@ forallLCIappend(ilist, indices, index, start);
        //@ indices = cons(index, indices);
        //@ assert(true == forall(ilist, (loopcontainedin)(indices, start)));
        //@ assert(true == byloop(ilist, indices, start));
        //@ nat_seq_append_len(ilist);
        //@ ilist = cons(i, ilist);
        //@ assert(true == loopcontainedin(indices, start, i));
        //@ assert(true == byloop(ilist, indices, start));
    }
    //@ list<int> olist = replicate_nat_seq(ilist);
    //@ loopedProp(olist, indices, ilist, bbs, start, busy);
    //@ assert(length(ilist) == CAPACITY);
    //@ assert(length(olist) == CAPACITY);
    //@ nat_seq_forall(olist, bbs, busy);
    //@ allbusy_no_free(bbs);
    //@ assert(contains(bbs, 0) == false);
    //@ destroy_nat_seq(ilist);
    //@ destroy_nat_seq(olist);
    return -1;
}

