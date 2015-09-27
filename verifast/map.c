


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
  
  @*/
  

/*@
      fixpoint bool isbusy(list<int> bbs, int i) { return (nth(i, bbs) != 0); }
      fixpoint bool loopcontainedin(list<int> xs, int start, int x) { return contains(xs, loop_l((int)(start + x))); }
      
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
    fixpoint bool byloop(list<int> ys, list<int> xs, int start) { return forall(ys, (loopcontainedin)(xs, start)); }
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

@*/

/*@

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

lemma void loopedBBS(list<int> olist, list<int> indices, list<int> ilist, list<int> bbs, int start)
requires nat_seq(olist) &*& true == forall(indices, (isbusy)(bbs)) &*& true == byloop(ilist, indices, start) &*& nat_seq(ilist)
     &*& (length(ilist) == CAPACITY) &*& (length(olist) <= CAPACITY) &*& 0 <= start &*& start < CAPACITY;
ensures true == forall(olist, (isbusy)(bbs)) &*& nat_seq(ilist) &*& nat_seq(olist);
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
        forall_mem(h, indices, (isbusy)(bbs));
        assert(true == isbusy(bbs, h));
        assert(true == forall(olist, (isbusy)(bbs)));
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
        loopedBBS(t, indices, ilist, bbs, start);
        assert(true == forall(t, (isbusy)(bbs)));
        nat_seq_cont(ilist, x);
        forall_mem(x, ilist, (loopcontainedin)(indices, start));
        assert(true == mem(h, indices));
        forall_mem(h, indices, (isbusy)(bbs));
        assert(true == isbusy(bbs, h));
        assert(true == forall(olist, (isbusy)(bbs)));
      }
      close nat_seq(olist);
  }
}

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

lemma void length_0_nil(list<int> lst)
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

fixpoint bool busyIfexists(list<int> bbs, int x) { return x < 0 || length(bbs) <= x || isbusy(bbs, x); }

lemma void nat_take_subarr_busyIE(list<int> nseq, list<int> arr)
requires nat_seq(nseq) &*& true == forall(nseq, (busyIfexists)(arr)) &*& length(arr) > 0;
ensures nat_seq(nseq) &*& true == forall(nseq, (busyIfexists)(take(length(arr) - 1, arr)));
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
          assert(true == busyIfexists(take(length(arr) -1, arr), h));
        } else {
          assert(length(arr) - 1 > 0);
          assert(nth(h, take(length(arr) -1, arr)) == nth(h, arr));
          assert(true == busyIfexists(take(length(arr) - 1, arr), h));
        }
      } else {
        if (h < length(arr) - 1) {
          assert(nth(h, take(length(arr) - 1, arr)) == nth(h, arr));
        } else {
          assert(length(take(length(arr) - 1, arr)) <= h);
        }
        assert(true == busyIfexists(take(length(arr) - 1, arr), h));
        nat_take_subarr_busyIE(t, arr);
      }
      close nat_seq(nseq);
      return;
  }
}

lemma void cons_take_take_cons(int head, list<int> tail, int n)
requires 0 <= n;
ensures cons(head, take(n, tail)) == take(n + 1, cons(head, tail));
{
  switch(tail) {
    case nil: return;
    case cons(h, t):
      return;
  }
}

lemma void if_exists_on_empty(list<int> nseq, list<int> arr)
requires length(arr) == 0;
ensures true == forall(nseq, (busyIfexists)(arr));
{
  switch(nseq) {
    case nil: return;
    case cons(h, t):
      assert(0 < h || h <= length(arr));
      assert(true == busyIfexists(arr, h));
      if_exists_on_empty(t, arr);
      return;
  }
}

lemma void append_take_cons(list<int> lst)
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

lemma void nth_len_append_cons(list<int> lst, int x)
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

lemma void nth_less_append_cons(int n, list<int> lst, int x)
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

lemma void busyIfexists_append1(list<int> seq, list<int> arr, int x)
requires true == forall(seq, (busyIfexists)(arr)) &*& x != 0;
ensures true == forall(seq, (busyIfexists)(append(arr, cons(x, nil))));
{
  switch(seq) {
    case nil: return;
    case cons(h, t):
      busyIfexists_append1(t, arr, x);
      if (h < 0) return;
      else if (h > length(arr)) return;
      else if (h == length(arr)) {
        nth_len_append_cons(arr, x);
        assert(nth(h, append(arr, cons(x, nil))) == x);
        assert(nth(h, append(arr, cons(x, nil))) != 0);
        return;
      } else {
        assert(nth(h, arr) != 0);
        nth_less_append_cons(h, arr, x);
        assert(nth(h, append(arr, cons(x, nil))) == nth(h, arr));
        return;
      }
  }
}

lemma void nat_subarr_busy_if_exists(list<int> nseq, list<int> arr, int arrhead)
requires nat_seq(nseq) &*& true == forall(nseq, (busyIfexists)(cons(arrhead, arr))) &*& length(arr) < length(nseq);
ensures nat_seq(nseq) &*& true == forall(nseq, (busyIfexists)(arr));
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
        assert(true == forall(t, (busyIfexists)(cons(arrhead, arr))));
        nat_take_subarr_busyIE(t, cons(arrhead, arr));
        assert(length(arr) == length(cons(arrhead, arr)) - 1);
        int ll = length(arr);
        length_nonnegative(arr);
        if (ll == 0) {
          if_exists_on_empty(nseq, arr);
        } else {
          cons_take_take_cons(arrhead, arr, ll - 1);
          assert(cons(arrhead, take(ll - 1, arr)) == take(ll, cons(arrhead, arr)));
          assert(cons(arrhead, take(length(arr) - 1, arr)) == take(length(cons(arrhead, arr)) - 1, cons(arrhead, arr)));
          nat_subarr_busy_if_exists(t, take(length(arr) - 1, arr), arrhead);
          assert(true == forall(t, (busyIfexists)(take(length(arr) - 1, arr))));
          assert(true == forall(t, (busyIfexists)(cons(arrhead, arr))));
          
          close nat_seq(nseq);
          nat_seq_cont(nseq, ll);
          open nat_seq(nseq);
          forall_mem(ll, nseq, (busyIfexists)(cons(arrhead, arr)));
          assert(true == busyIfexists(cons(arrhead, arr), ll));
          assert(true == busyIfexists(arr, ll - 1));
          assert(nth(ll - 1, arr) != 0);
          
          busyIfexists_append1(t, take(ll - 1, arr), nth(ll - 1, arr));
          assert(true == forall(t, (busyIfexists)(append(take(ll - 1, arr), cons(nth(ll - 1, arr), nil)))));
          append_take_cons(arr);
          assert(arr == append(take(ll - 1, arr), cons(nth(ll - 1, arr), nil)));
          
          assert(true == forall(t, (busyIfexists)(arr)));
          assert(h == length(nseq) - 1);
          assert(length(arr) <= h);
          assert(true == busyIfexists(arr, h));
        }
      }
      close nat_seq(nseq);
      return;
  }
}

lemma void busy_busyIfexists(list<int> seq, list<int> arr)
requires true == forall(seq, (isbusy)(arr));
ensures true == forall(seq, (busyIfexists)(arr));
{
  switch(seq) {
    case nil: return;
    case cons(h, t):
      assert(true == isbusy(arr, h));
      assert(true == busyIfexists(arr, h));
      busy_busyIfexists(t, arr);
      return;
  }
}

lemma void nat_seq_busyIfexists_busy(list<int> nseq, list<int> arr)
requires nat_seq(nseq) &*& true == forall(nseq, (busyIfexists)(arr)) &*& length(nseq) <= length(arr);
ensures nat_seq(nseq) &*& true == forall(nseq, (isbusy)(arr));
{
  switch(nseq) {
    case nil: return;
    case cons(h, t):
      nat_seq_ge_0(nseq);
      assert(0 <= h);
      nat_seq_head_len(nseq);
      assert(h < length(arr));
      assert(true == busyIfexists(arr, h));
      assert(true == isbusy(arr, h));
      open nat_seq(nseq);
      if (h == 0) {
        assert(t == nil);
      } else {
        nat_seq_busyIfexists_busy(t, arr);
      }
      close nat_seq(nseq);
  }
}

lemma void nat_subseq_busy_subarr(list<int> nseq, int shead, list<int> arr, int arrhead)
requires nat_seq(cons(shead, nseq)) &*& true == forall(cons(shead, nseq), (isbusy)(cons(arrhead, arr))) &*& length(nseq) == length(arr);
ensures nat_seq(cons(shead, nseq)) &*& true == forall(nseq, (isbusy)(arr));
{
  assert(true == forall(cons(shead, nseq), (isbusy)(cons(arrhead, arr))));
  busy_busyIfexists(cons(shead, nseq), cons(arrhead, arr));
  assert(true == forall(cons(shead, nseq), (busyIfexists)(cons(arrhead, arr))));
  nat_subarr_busy_if_exists(cons(shead, nseq), arr, arrhead);
  assert(true == forall(nseq, (busyIfexists)(arr)));
  open nat_seq(cons(shead, nseq));
  if (shead == 0) {
    assert(nseq == nil);
  } else {
    nat_seq_busyIfexists_busy(nseq, arr);
  }
  close nat_seq(cons(shead, nseq));
  assert(true == forall(nseq, (isbusy)(arr)));
}

fixpoint bool busyx(int x) {return (x != 0); }

lemma void allBusy(list<int> nseq, list<int> bbs)
requires nat_seq(nseq) &*& true == forall(nseq, (isbusy)(bbs)) &*& length(nseq) == length(bbs);
ensures nat_seq(nseq) &*& true == forall(bbs, busyx);
{
  switch(nseq) {
    case nil:
      assert(length(bbs) == 0);
      switch(bbs) {
        case nil:
          return;
        case cons(bh, bt):
          length_positive(bt);
          assert(length(bbs) == length(bt) + 1);
          assert(length(bbs) > 0);
          return;
      }
    case cons(h, t) :
      switch(bbs) {
        case nil:
          return;
        case cons(bh, bt):
          nat_seq_cont(nseq, 0);
          forall_mem(0, nseq, (isbusy)(bbs));
          assert(true == isbusy(bbs, 0));
          assert(nth(0, bbs) != 0);
          assert(bh == nth(0, bbs));
          assert(bh != 0);
          nat_subseq_busy_subarr(t, h, bt, bh);
          assert(true == forall(t, (isbusy)(bt)));
          open nat_seq(nseq);
          if (h == 0) {
            assert(t == nil);
            assert(length(bbs) == 1);
            assert(length(bt) == 0);
            length_0_nil(bt);
            assert(bt == nil);
          } else {
            allBusy(t, bt);
          }
          assert(true == forall(bt, busyx));
          close nat_seq(nseq);
          return;
      }
  }
}

lemma void allbusy_no_free(list<int> bbs)
requires true == forall(bbs, busyx);
ensures false == contains(bbs, 0);
{
  switch(bbs) {
    case nil: return;
    case cons(h, t):
      allbusy_no_free(t);
      return;
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
               true == forall(indices, (isbusy)(bbs)) &*& true == byloop(ilist, indices, start) &*&
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
    //@ loopedBBS(olist, indices, ilist, bbs, start);
    //@ assert(length(ilist) == CAPACITY);
    //@ assert(length(olist) == CAPACITY);
    //@ allBusy(olist, bbs);
    //@ allbusy_no_free(bbs);
    //@ assert(contains(bbs, 0) == false);
    //@ destroy_nat_seq(ilist);
    //@ destroy_nat_seq(olist);
    return -1;
}