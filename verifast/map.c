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
  ensures true == bkhas_key(bks, key);
  {
    switch(bks) {
      case nil: return;
      case cons(h, t):
        if (i == 0) {
        } else {
          does_have_key(i - 1, key, t);
        }
        assert(true == bkhas_key(bks, key));
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
    
  fixpoint bool bkhas_key(list<busy_key> bks, int key) {
    switch(bks) {
      case nil: return false;
      case cons(h, t):
        return (bk_busybit(h) != 0 && bk_key(h) == key) || bkhas_key(t, key);
    }
  }
  
  fixpoint bool not_a_valid_key(int key, busy_key bk) {
    return bk_key(bk) != key || bk_busybit(bk) == 0;
  }

  lemma void forall_no_valid_key_has_no_key(list<busy_key> bks, int key)
  requires true == forall(bks, (not_a_valid_key)(key));
  ensures false == bkhas_key(bks, key);
  {
    switch(bks) {
      case nil: return;
      case cons(h, t):
        forall_no_valid_key_has_no_key(t, key);
        return;
    }
  }
  
  lemma void destroy_bkeys(list<busy_key> bks)
  requires bkeys(bks, _, _);
  ensures true;
  {
    open bkeys(bks, _, _);
    switch(bks) {
      case nil: return;
      case cons(h, t): destroy_bkeys(t); return;
    }
  }

@*/

int find_key(int* busybits, int* keys, int start, int key)
     //@ requires 0 <= start &*& start < CAPACITY &*& ints(busybits, CAPACITY, ?bbs) &*& ints(keys, CAPACITY, ?ks) &*& bkeys(?bks, bbs, ks);
     //@ ensures ints(busybits, CAPACITY, bbs) &*& ints(keys, CAPACITY, ks) &*& bkeys(bks, bbs, ks) &*& \
         (bkhas_key(bks, key) ? bk_key(nth(result, bks)) == key &*& bk_busybit(nth(result, bks)) != 0 &*& 0 <= result &*& result < CAPACITY : result == -1);
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
    //@ ensures ints(busybits, CAPACITY, bbs) &*& \
        (contains(bbs, 0) ? nth(result, bbs) == 0 &*& 0 <= result &*& result < CAPACITY : result == -1);
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

/*@ 

inductive record = rec_triple(int busybit, int key, int value);

fixpoint int rec_bb(record r) {
  switch(r) { case rec_triple(bb, k, v): return bb; }
}

fixpoint int rec_key(record r) {
  switch(r) { case rec_triple(bb, k, v): return k; }
}

fixpoint int rec_val(record r) {
  switch(r) { case rec_triple(bb, k, v): return v; }
}

fixpoint bool has_key(list<record> recs, int key) {
  switch(recs) {
    case nil: return false;
    case cons(h, t):
      return (rec_bb(h) != 0 && rec_key(h) == key) ? true : has_key(t, key);
  }
}

fixpoint int get_val(list<record> recs, int key) {
  switch(recs) {
    case nil: return default_value<int>;
    case cons(h, t):
      return (rec_bb(h) != 0 && rec_key(h) == key) ? rec_val(h) : get_val(t, key);
  }
}

fixpoint bool no_dubs(list<record> recs) {
  switch(recs) {
    case nil: return true;
    case cons(h, t):
      return (rec_bb(h) == 0 || !has_key(t, rec_key(h))) && no_dubs(t);
  }
}

predicate records(list<int> bbs, list<int> ks, list<int> vals, list<record> recs) =
  switch(recs) {
    case nil: return bbs == nil &*& ks == nil &*& vals == nil;
    case cons(rh, rt):
      return bbs != nil &*& ks != nil &*& vals != nil &*&
             rh == rec_triple(head(bbs), head(ks), head(vals)) &*&
             records(tail(bbs), tail(ks), tail(vals), rt);
  };

predicate mapping_(int* busybits, int* keys, int* values, list<record> recs) = 
  ints(busybits, CAPACITY, ?bbs) &*& ints(keys, CAPACITY, ?ks) &*& ints(values, CAPACITY, ?vals) &*&
  records(bbs, ks, vals, recs) &*& true == no_dubs(recs);

lemma void records_same_length(list<int> bbs, list<int> ks, list<int> vals, list<record> recs)
requires records(bbs, ks, vals, recs);
ensures records(bbs, ks, vals, recs) &*& length(recs) == length(bbs) &*& length(recs) == length(ks) &*& length(recs) == length(vals);
{
  open records(bbs, ks, vals, recs);
  switch(recs) {
    case nil: break;
    case cons(h, t):
      cons_head_tail(bbs);
      cons_head_tail(ks);
      cons_head_tail(vals);
      records_same_length(tail(bbs), tail(ks), tail(vals), t);
      break;
  }
  close records(bbs, ks, vals, recs);
}

lemma list<busy_key> make_bkeys_from_recs(list<int> bbs, list<int> ks, list<int> vals, list<record> recs)
requires records(bbs, ks, vals, recs);
ensures records(bbs, ks, vals, recs) &*& bkeys(result, bbs, ks);
{
  switch(recs) {
    case nil:
      open records(bbs, ks, vals, recs);
      close bkeys(nil, bbs, ks);
      close records(bbs, ks, vals, recs);
      return nil;
    case cons(h, t):
      open records(bbs, ks, vals, recs);
      list<busy_key> bkt = make_bkeys_from_recs(tail(bbs), tail(ks), tail(vals), t);
      list<busy_key> ret = cons(bkpair(head(bbs), head(ks)), bkt);
      close bkeys(ret, bbs, ks);
      close records(bbs, ks, vals, recs);
      return ret;
  }
}


lemma void nth_bbs_keys_vals_recs(int n, list<int> bbs, list<int> ks, list<int> vals, list<record> recs)
requires records(bbs, ks, vals, recs) &*& 0 <= n &*& n < length(recs);
ensures records(bbs, ks, vals, recs) &*& rec_key(nth(n, recs)) == nth(n, ks) &*&
        rec_bb(nth(n, recs)) == nth(n, bbs) &*& rec_val(nth(n, recs)) == nth(n, vals);
{
  open records(bbs, ks, vals, recs);
  switch(recs) {
    case nil:
      break;
    case cons(h, t):
      assert(ks != nil);
      assert(bbs != nil);
      assert(vals != nil);
      if (n == 0) {
        nth_0_head(ks);
        nth_0_head(bbs);
        nth_0_head(vals);
      } else {
        nth_bbs_keys_vals_recs(n - 1, tail(bbs), tail(ks), tail(vals), t);
        nth_cons(n, tail(bbs), head(bbs));
        nth_cons(n, tail(ks), head(ks));
        nth_cons(n, tail(vals), head(vals));
        nth_cons(n, t, h);
        cons_head_tail(ks);
        cons_head_tail(bbs);
        cons_head_tail(vals);
      }
      break;
  }
  close records(bbs, ks, vals, recs);
}
  

lemma void found_is_the_key_val(list<int> bbs, list<int> ks, list<int> vals, list<record> recs, int key, int index)
requires records(bbs, ks, vals, recs) &*& nth(index, bbs) != 0 &*& nth(index, ks) == key &*& true == no_dubs(recs) &*& 0 <= index &*& index < length(recs);
ensures records(bbs, ks, vals, recs) &*& true == has_key(recs, key) &*& get_val(recs, key) == nth(index, vals);
{
  open records(bbs, ks, vals, recs);
  switch(recs) {
    case nil: break;
    case cons(h, t):
      if (index == 0) {
        nth_0_head(bbs);
        nth_0_head(ks);
        nth_0_head(vals);
        assert(true == has_key(recs, key));
      } else {
        nth_cons(index, tail(bbs), head(bbs));
        nth_cons(index, tail(ks), head(ks));
        nth_cons(index, tail(vals), head(vals));
        cons_head_tail(bbs);
        cons_head_tail(ks);
        cons_head_tail(vals);
        found_is_the_key_val(tail(bbs), tail(ks), tail(vals), t, key, index - 1);
      }
      break;
  }
  close records(bbs, ks, vals, recs);
}

lemma void bkhas_key2has_key(list<record> recs, list<busy_key> bks, int key)
requires bkeys(bks, ?bbs, ?ks) &*& records(bbs, ks, ?vals, recs);
ensures bkeys(bks, bbs, ks) &*& records(bbs, ks, vals, recs) &*& has_key(recs, key) == bkhas_key(bks, key);
{
  open bkeys(bks, bbs, ks);
  open records(bbs, ks, vals, recs);
  switch(bks) {
    case nil: break;
    case cons(h, t):
      if (bk_busybit(h) != 0 && bk_key(h) == key) {
      } else {
        cons_head_tail(recs);
        bkhas_key2has_key(tail(recs), t, key);
      }
      break;
  }
  close records(bbs, ks, vals, recs);
  close bkeys(bks, bbs, ks);
}

inductive kvpair = kvpair_constr(int, int);

fixpoint int kv_key(kvpair kv) { switch(kv) { case kvpair_constr(k, v): return k; }}
fixpoint int kv_value(kvpair kv) { switch(kv) { case kvpair_constr(k, v): return v; }}

fixpoint bool recs_contain_kv(list<record> recs, kvpair kv) {
  switch(recs) {
    case nil: return false;
    case cons(h, t):
    return (rec_key(h) == kv_key(kv) && rec_bb(h) != 0 && rec_val(h) == kv_value(kv)) || recs_contain_kv(t, kv);
  }
}

fixpoint bool kvs_contain_rec(list<kvpair> kvs, record rec) {
  switch(kvs) {
    case nil: return !(rec_bb(rec) != 0);
    case cons(h, t):
      return rec_bb(rec) != 0 ? (kv_key(h) == rec_key(rec) ? kv_value(h) == rec_val(rec) 
                                                           : kvs_contain_rec(t, rec))
                              : true;
  }
}

fixpoint bool kv_has_key(list<kvpair> kvs, int key) {
  switch(kvs) {
    case nil: return false;
    case cons(h, t):
      return kv_key(h) == key || kv_has_key(t, key);
  }
}

fixpoint int kv_get_val(list<kvpair> kvs, int key) {
  switch(kvs) {
    case nil: return default_value<int>;
    case cons(h, t):
      return kv_key(h) == key ? kv_value(h) : kv_get_val(t, key);
  }
}

fixpoint bool kv_no_dubs(list<kvpair> kvs) {
  switch(kvs) {
    case nil: return true;
    case cons(h, t):
      return !kv_has_key(t, kv_key(h)) && kv_no_dubs(t);
  }
}

predicate recs_mapping(list<record> recs, list<kvpair> kvs) =
  true == forall(kvs, (recs_contain_kv)(recs)) &*& true == forall(recs, (kvs_contain_rec)(kvs))
  &*& true == kv_no_dubs(kvs);

predicate mapping(int* busybits, int* keys, int* values, list<kvpair> kvs) =
  mapping_(busybits, keys, values, ?recs) &*& recs_mapping(recs, kvs);

lemma void kvs_contain_rec_2_kv_has_key(list<kvpair> kvs, record rec)
requires true == kvs_contain_rec(kvs, rec) &*& rec_bb(rec) != 0;
ensures true == kv_has_key(kvs, rec_key(rec));
{
  switch(kvs){
    case nil: return;
    case cons(h, t):
      if (kv_key(h) == rec_key(rec)) return;
      else kvs_contain_rec_2_kv_has_key(t, rec);
      return;
  }
}

lemma void recs_has_key2kv_has_key(list<record> recs, list<kvpair> kvs, int key)
requires true == forall(recs, (kvs_contain_rec)(kvs)) &*& true == has_key(recs, key);
ensures true == kv_has_key(kvs, key);
{
  switch(recs) {
    case nil:
      assert(false == has_key(recs, key));
      break;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
        assert(true == kvs_contain_rec(kvs, h));
        kvs_contain_rec_2_kv_has_key(kvs, h);
        assert(true == kv_has_key(kvs, key));
      } else {
        assert(true == forall(t, (kvs_contain_rec)(kvs)));
        assert(true == has_key(t, key));
        recs_has_key2kv_has_key(t, kvs, key);
      }
      break;
  }
}

lemma void recs_contain_kv2has_key(list<record> recs, kvpair kv)
requires true == recs_contain_kv(recs, kv);
ensures true == has_key(recs, kv_key(kv));
{
  switch(recs) {
    case nil: return;
    case cons(h, t): 
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)) return;
      else recs_contain_kv2has_key(t, kv);
      return;
  }
}

lemma void kv_has_key2recs_has_key(list<kvpair> kvs, list<record> recs, int key)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& true == kv_has_key(kvs, key);
ensures true == has_key(recs, key);
{
  switch(kvs) {
    case nil:
      assert(false == kv_has_key(kvs, key));
      return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(true == recs_contain_kv(recs, h));
        recs_contain_kv2has_key(recs, h);
        assert(true == has_key(recs, key));
      } else {
        assert(true == forall(t, (recs_contain_kv)(recs)));
        assert(true == kv_has_key(t, key));
        kv_has_key2recs_has_key(t, recs, key);
      }
      return;
  }
}

lemma void recs_has_key_eq_kv_has_key(list<record> recs, list<kvpair> kvs, int key)
requires recs_mapping(recs, kvs);
ensures recs_mapping(recs, kvs) &*& has_key(recs, key) == kv_has_key(kvs, key);
{
  open recs_mapping(recs, kvs);
  if (has_key(recs, key)) {
    recs_has_key2kv_has_key(recs, kvs, key);
  } else {
    if (kv_has_key(kvs, key)) {
      kv_has_key2recs_has_key(kvs, recs, key);
    } else {
    }
  }
  close recs_mapping(recs, kvs);
}

fixpoint list<record> remove_key(list<record> recs, int key) {
  switch(recs) {
    case nil: return nil;
    case cons(h, t):
      return rec_bb(h) != 0 && rec_key(h) == key ? cons(rec_triple(0, rec_key(h), rec_val(h)),
                                                        remove_key(t, key))
                                                 : cons(h, remove_key(t, key));
  }
}

lemma void remove_key_removes_key(list<record> recs, int key)
requires true;
ensures false == has_key(remove_key(recs, key), key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      remove_key_removes_key(t, key);
      return;
  }
}

lemma void remove_key_preserves_has_not_key(list<record> recs, int key_rem, int key_abs)
requires false == has_key(recs, key_abs);
ensures false == has_key(remove_key(recs, key_rem), key_abs);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key_abs) {
      } else {
        remove_key_preserves_has_not_key(t, key_rem, key_abs);
      }
      return;
  }
}

lemma void remove_key_preserves_has_key(list<record> recs, int key_rem, int key)
requires key_rem != key;
ensures has_key(remove_key(recs, key_rem), key) == has_key(recs, key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
      } else {
        remove_key_preserves_has_key(t, key_rem, key);
      }
      return;
  }
}

lemma void remove_key_preserves_get_val(list<record> recs, int key_rem, int key)
requires key_rem != key;
ensures get_val(remove_key(recs, key_rem), key) == get_val(recs, key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
      } else {
        remove_key_preserves_get_val(t, key_rem, key);
      }
      return;
  }
}

lemma void remove_key_preserves_no_dubs(list<record> recs, int key)
requires true == no_dubs(recs);
ensures true == no_dubs(remove_key(recs, key));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      remove_key_preserves_no_dubs(t, key);
      if (rec_bb(h) != 0) {
        remove_key_preserves_has_not_key(t, key, rec_key(h));
      }
      return;
  }
}

lemma void kvs_tail_contains_rest(list<record> recs, list<kvpair> kvs, kvpair kv)
requires true == forall(recs, (kvs_contain_rec)(cons(kv, kvs))) &*& false == has_key(recs, kv_key(kv));
ensures true == forall(recs, (kvs_contain_rec)(kvs));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)) {
        assert(true == has_key(recs, kv_key(kv)));
      } else {
        if (rec_bb(h) != 0) {
          switch(cons(kv, kvs)) {
            case nil: break;
            case cons(kvh, kvt):
              assert(true == kvs_contain_rec(kvs, h));
              break;
          }
        } else {
          switch(kvs) {
            case nil: break;
            case cons(kvh, kvt) : break;
          }
          assert(true == kvs_contain_rec(kvs, h));
        }
        assert(true == kvs_contain_rec(kvs, h));
        kvs_tail_contains_rest(t, kvs, kv);
      }
      return;
  }
}

lemma void remove_key_preserves_rec2kv_inj(list<record> recs, list<kvpair> kvs, int key)
requires true == forall(recs, (kvs_contain_rec)(kvs));
ensures true == forall(remove_key(recs, key), (kvs_contain_rec)(kvs));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      remove_key_preserves_rec2kv_inj(t, kvs, key);
      if (rec_bb(h) != 0 && rec_key(h) == key) {
        switch(kvs) {
          case nil: break;
          case cons(kvh, kvt): break;
        }
      }
      return;
  }
}

lemma void remove_key_preserves_recs_contain_kv(list<record> recs, kvpair kv, int key)
requires true == recs_contain_kv(recs, kv) &*& kv_key(kv) != key;
ensures true == recs_contain_kv(remove_key(recs, key), kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv) && rec_val(h) == kv_value(kv)) {
      } else {
        remove_key_preserves_recs_contain_kv(t, kv, key);
      }
      return;
  }
}

lemma void remove_key_preserves_kv2rec_inj(list<kvpair> kvs, list<record> recs, int key)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& false == kv_has_key(kvs, key);
ensures true == forall(kvs, (recs_contain_kv)(remove_key(recs, key)));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(true == kv_has_key(kvs, key));
      } else {
        remove_key_preserves_recs_contain_kv(recs, h, key);
        remove_key_preserves_kv2rec_inj(t, recs, key);
      }
      return;
  }
}

lemma void remove_head_key_preserves_mapping(list<record> recs, kvpair kv, list<kvpair> kvs)
requires recs_mapping(recs, cons(kv, kvs)) &*& true == no_dubs(recs) &*& true == kv_no_dubs(cons(kv, kvs));
ensures recs_mapping(recs, cons(kv, kvs)) &*& recs_mapping(remove_key(recs, kv_key(kv)), kvs);
{
  open recs_mapping(recs, cons(kv, kvs));
  
  remove_key_preserves_rec2kv_inj(recs, cons(kv, kvs), kv_key(kv));
  remove_key_removes_key(recs, kv_key(kv));
  kvs_tail_contains_rest(remove_key(recs, kv_key(kv)), kvs, kv);
  remove_key_preserves_kv2rec_inj(kvs, recs, kv_key(kv));
  
  close recs_mapping(recs, cons(kv, kvs));
  close recs_mapping(remove_key(recs, kv_key(kv)), kvs);
}

lemma void recs_no_key_no_kv(list<record> recs, kvpair kv)
requires false == has_key(recs, kv_key(kv));
ensures false == recs_contain_kv(recs, kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)){
      } else {
        recs_no_key_no_kv(t, kv);
      }
      return;
  }
}

lemma void recs_contain_kv_right_get_val(list<record> recs, kvpair kv)
requires true == recs_contain_kv(recs, kv) &*& true == no_dubs(recs);
ensures get_val(recs, kv_key(kv)) == kv_value(kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)) {
        assert(get_val(recs, kv_key(kv)) == rec_val(h));
        assert(false == has_key(t, kv_key(kv)));
        recs_no_key_no_kv(t, kv);
        assert(false == recs_contain_kv(t, kv));
        assert(rec_val(h) == kv_value(kv));
      } else {
        recs_contain_kv_right_get_val(t, kv);
      }
      return;
  }
}

lemma void recs_get_val_eq_kv_get_val(list<record> recs, list<kvpair> kvs, int key)
requires recs_mapping(recs, kvs) &*& true == no_dubs(recs) &*& true == kv_no_dubs(kvs) &*& true == has_key(recs, key);
ensures recs_mapping(recs, kvs) &*& get_val(recs, key) == kv_get_val(kvs, key);
{
  switch(kvs) {
    case nil:
      assert(false == kv_has_key(kvs, key));
      if (has_key(recs, key)) {
        open recs_mapping(recs, kvs);
        recs_has_key2kv_has_key(recs, kvs, key);
        close recs_mapping(recs, kvs);
      }
      assert(false == has_key(recs, key));
      return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(kv_get_val(kvs, key) == kv_value(h));
        open recs_mapping(recs, kvs);
        recs_contain_kv_right_get_val(recs, h);
        close recs_mapping(recs, kvs);
        assert(get_val(recs, key) == kv_value(h));
      } else {
        remove_head_key_preserves_mapping(recs, h, t);
        remove_key_preserves_no_dubs(recs, kv_key(h));
        remove_key_preserves_has_key(recs, kv_key(h), key);
        recs_get_val_eq_kv_get_val(remove_key(recs, kv_key(h)), t, key);
        remove_key_preserves_get_val(recs, kv_key(h), key);
        open recs_mapping(remove_key(recs, kv_key(h)), t);
      }
      return;
  }
}
@*/

int get(int* busybits, int* keys, int* values, int key)
//@ requires mapping(busybits, keys, values, ?kvs);
//@ ensures mapping(busybits, keys, values, kvs) &*& \
            (kv_has_key(kvs, key) ? result == kv_get_val(kvs, key) : result == -1);
{
    //@ open mapping(busybits, keys, values, kvs);
    //@ open mapping_(busybits, keys, values, ?recs);
    //@ open recs_mapping(recs, kvs);
    //@ assert records(?bbs, ?ks, ?vals, recs);
    //@ list<busy_key> bks = make_bkeys_from_recs(bbs, ks, vals, recs);
    int start = loop(key);
    int index = find_key(busybits, keys, start, key);

    if (-1 == index)
    {   
        //@ bkhas_key2has_key(recs, bks, key);
        //@ close recs_mapping(recs, kvs);
        //@ assert(false == has_key(recs, key));
        //@ recs_has_key_eq_kv_has_key(recs, kvs, key);
        //@ assert(false == kv_has_key(kvs, key));
        //@ close mapping_(busybits, keys, values, recs);
        //@ close mapping(busybits, keys, values, kvs);
        //@ destroy_bkeys(bks);
        return -1;
    }
    int val = values[index];
    //@ records_same_length(bbs, ks, vals, recs);
    //@ bkeys_len_eq(bks, bbs, ks);
    //@ nth_bbs_keys_bkeys(index, bbs, ks, bks);
    //@ found_is_the_key_val(bbs, ks, vals, recs, key, index);
    //@ close recs_mapping(recs, kvs);
    //@ recs_get_val_eq_kv_get_val(recs, kvs, key);
    //@ assert(true == has_key(recs, key));
    //@ recs_has_key_eq_kv_has_key(recs, kvs, key);
    //@ assert(true == kv_has_key(kvs, key));
    //@ assert(nth(index, vals) == get_val(recs, key));
    //@ close mapping_(busybits, keys, values, recs);
    //@ close mapping(busybits, keys, values, kvs);
    //@ destroy_bkeys(bks);
    return val;
}

