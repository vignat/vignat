//@ #include <list.gh>
//@ #include <listex.gh>
//@ #include "nat_seq.gh"
//@ #include "stdex.gh"
//@ #include "nth_prop.gh"

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
  
  @*/

/*@

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

fixpoint bool rec_has_key(list<record> recs, int key) {
  switch(recs) {
    case nil: return false;
    case cons(h, t):
      return (rec_bb(h) != 0 && rec_key(h) == key) ? true : rec_has_key(t, key);
  }
}

fixpoint int rec_get_val(list<record> recs, int key) {
  switch(recs) {
    case nil: return default_value<int>;
    case cons(h, t):
      return (rec_bb(h) != 0 && rec_key(h) == key) ? rec_val(h) : rec_get_val(t, key);
  }
}

fixpoint bool no_dubs(list<record> recs) {
  switch(recs) {
    case nil: return true;
    case cons(h, t):
      return (rec_bb(h) == 0 || !rec_has_key(t, rec_key(h))) && no_dubs(t);
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
ensures records(bbs, ks, vals, recs) &*& true == rec_has_key(recs, key) &*& rec_get_val(recs, key) == nth(index, vals);
{
  open records(bbs, ks, vals, recs);
  switch(recs) {
    case nil: break;
    case cons(h, t):
      if (index == 0) {
        nth_0_head(bbs);
        nth_0_head(ks);
        nth_0_head(vals);
        assert(true == rec_has_key(recs, key));
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

lemma void bkhas_key2rec_has_key(list<record> recs, list<busy_key> bks, int key)
requires bkeys(bks, ?bbs, ?ks) &*& records(bbs, ks, ?vals, recs);
ensures bkeys(bks, bbs, ks) &*& records(bbs, ks, vals, recs) &*& rec_has_key(recs, key) == bkhas_key(bks, key);
{
  open bkeys(bks, bbs, ks);
  open records(bbs, ks, vals, recs);
  switch(bks) {
    case nil: break;
    case cons(h, t):
      if (bk_busybit(h) != 0 && bk_key(h) == key) {
      } else {
        cons_head_tail(recs);
        bkhas_key2rec_has_key(tail(recs), t, key);
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

fixpoint bool has_key(list<kvpair> kvs, int key) {
  switch(kvs) {
    case nil: return false;
    case cons(h, t):
      return kv_key(h) == key || has_key(t, key);
  }
}

fixpoint int get_val(list<kvpair> kvs, int key) {
  switch(kvs) {
    case nil: return default_value<int>;
    case cons(h, t):
      return kv_key(h) == key ? kv_value(h) : get_val(t, key);
  }
}

fixpoint bool kv_no_dubs(list<kvpair> kvs) {
  switch(kvs) {
    case nil: return true;
    case cons(h, t):
      return !has_key(t, kv_key(h)) && kv_no_dubs(t);
  }
}

predicate recs_mapping(list<record> recs, list<kvpair> kvs) =
  true == forall(kvs, (recs_contain_kv)(recs)) &*& true == forall(recs, (kvs_contain_rec)(kvs))
  &*& true == kv_no_dubs(kvs);

predicate mapping(int* busybits, int* keys, int* values, list<kvpair> kvs) =
  mapping_(busybits, keys, values, ?recs) &*& recs_mapping(recs, kvs);

lemma void kvs_contain_rec_2_has_key(list<kvpair> kvs, record rec)
requires true == kvs_contain_rec(kvs, rec) &*& rec_bb(rec) != 0;
ensures true == has_key(kvs, rec_key(rec));
{
  switch(kvs){
    case nil: return;
    case cons(h, t):
      if (kv_key(h) == rec_key(rec)) return;
      else kvs_contain_rec_2_has_key(t, rec);
      return;
  }
}

lemma void rec_has_key2has_key(list<record> recs, list<kvpair> kvs, int key)
requires true == forall(recs, (kvs_contain_rec)(kvs)) &*& true == rec_has_key(recs, key);
ensures true == has_key(kvs, key);
{
  switch(recs) {
    case nil:
      assert(false == rec_has_key(recs, key));
      break;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
        assert(true == kvs_contain_rec(kvs, h));
        kvs_contain_rec_2_has_key(kvs, h);
        assert(true == has_key(kvs, key));
      } else {
        assert(true == forall(t, (kvs_contain_rec)(kvs)));
        assert(true == rec_has_key(t, key));
        rec_has_key2has_key(t, kvs, key);
      }
      break;
  }
}

lemma void recs_contain_kv2rec_has_key(list<record> recs, kvpair kv)
requires true == recs_contain_kv(recs, kv);
ensures true == rec_has_key(recs, kv_key(kv));
{
  switch(recs) {
    case nil: return;
    case cons(h, t): 
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)) return;
      else recs_contain_kv2rec_has_key(t, kv);
      return;
  }
}

lemma void has_key2rec_has_key(list<kvpair> kvs, list<record> recs, int key)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& true == has_key(kvs, key);
ensures true == rec_has_key(recs, key);
{
  switch(kvs) {
    case nil:
      assert(false == has_key(kvs, key));
      return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(true == recs_contain_kv(recs, h));
        recs_contain_kv2rec_has_key(recs, h);
        assert(true == rec_has_key(recs, key));
      } else {
        assert(true == forall(t, (recs_contain_kv)(recs)));
        assert(true == has_key(t, key));
        has_key2rec_has_key(t, recs, key);
      }
      return;
  }
}

lemma void rec_has_key_eq_has_key(list<record> recs, list<kvpair> kvs, int key)
requires recs_mapping(recs, kvs);
ensures recs_mapping(recs, kvs) &*& rec_has_key(recs, key) == has_key(kvs, key);
{
  open recs_mapping(recs, kvs);
  if (rec_has_key(recs, key)) {
    rec_has_key2has_key(recs, kvs, key);
  } else {
    if (has_key(kvs, key)) {
      has_key2rec_has_key(kvs, recs, key);
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
ensures false == rec_has_key(remove_key(recs, key), key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      remove_key_removes_key(t, key);
      return;
  }
}

lemma void remove_key_abscent_id(list<record> recs, int key)
requires false == rec_has_key(recs, key);
ensures recs == remove_key(recs, key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      remove_key_abscent_id(t, key);
      return;
  }
}

lemma void remove_key_preserves_has_not_key(list<record> recs, int key_rem, int key_abs)
requires false == rec_has_key(recs, key_abs);
ensures false == rec_has_key(remove_key(recs, key_rem), key_abs);
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

lemma void remove_key_preserves_rec_has_key(list<record> recs, int key_rem, int key)
requires key_rem != key;
ensures rec_has_key(remove_key(recs, key_rem), key) == rec_has_key(recs, key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
      } else {
        remove_key_preserves_rec_has_key(t, key_rem, key);
      }
      return;
  }
}

lemma void remove_key_preserves_rec_get_val(list<record> recs, int key_rem, int key)
requires key_rem != key;
ensures rec_get_val(remove_key(recs, key_rem), key) == rec_get_val(recs, key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
      } else {
        remove_key_preserves_rec_get_val(t, key_rem, key);
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
requires true == forall(recs, (kvs_contain_rec)(cons(kv, kvs))) &*& false == rec_has_key(recs, kv_key(kv));
ensures true == forall(recs, (kvs_contain_rec)(kvs));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)) {
        assert(true == rec_has_key(recs, kv_key(kv)));
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
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& false == has_key(kvs, key);
ensures true == forall(kvs, (recs_contain_kv)(remove_key(recs, key)));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(true == has_key(kvs, key));
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
requires false == rec_has_key(recs, kv_key(kv));
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

lemma void recs_contain_kv_right_rec_get_val(list<record> recs, kvpair kv)
requires true == recs_contain_kv(recs, kv) &*& true == no_dubs(recs);
ensures rec_get_val(recs, kv_key(kv)) == kv_value(kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv)) {
        assert(rec_get_val(recs, kv_key(kv)) == rec_val(h));
        assert(false == rec_has_key(t, kv_key(kv)));
        recs_no_key_no_kv(t, kv);
        assert(false == recs_contain_kv(t, kv));
        assert(rec_val(h) == kv_value(kv));
      } else {
        recs_contain_kv_right_rec_get_val(t, kv);
      }
      return;
  }
}

lemma void rec_get_val_eq_get_val(list<record> recs, list<kvpair> kvs, int key)
requires recs_mapping(recs, kvs) &*& true == no_dubs(recs) &*& true == kv_no_dubs(kvs) &*& true == rec_has_key(recs, key);
ensures recs_mapping(recs, kvs) &*& rec_get_val(recs, key) == get_val(kvs, key);
{
  switch(kvs) {
    case nil:
      assert(false == has_key(kvs, key));
      if (rec_has_key(recs, key)) {
        open recs_mapping(recs, kvs);
        rec_has_key2has_key(recs, kvs, key);
        close recs_mapping(recs, kvs);
      }
      assert(false == rec_has_key(recs, key));
      return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(get_val(kvs, key) == kv_value(h));
        open recs_mapping(recs, kvs);
        recs_contain_kv_right_rec_get_val(recs, h);
        close recs_mapping(recs, kvs);
        assert(rec_get_val(recs, key) == kv_value(h));
      } else {
        remove_head_key_preserves_mapping(recs, h, t);
        remove_key_preserves_no_dubs(recs, kv_key(h));
        remove_key_preserves_rec_has_key(recs, kv_key(h), key);
        rec_get_val_eq_get_val(remove_key(recs, kv_key(h)), t, key);
        remove_key_preserves_rec_get_val(recs, kv_key(h), key);
        open recs_mapping(remove_key(recs, kv_key(h)), t);
      }
      return;
  }
}
@*/

int get(int* busybits, int* keys, int* values, int key)
//@ requires mapping(busybits, keys, values, ?kvs);
//@ ensures mapping(busybits, keys, values, kvs) &*& \
            (has_key(kvs, key) ? result == get_val(kvs, key) : result == -1);
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
        //@ bkhas_key2rec_has_key(recs, bks, key);
        //@ close recs_mapping(recs, kvs);
        //@ assert(false == rec_has_key(recs, key));
        //@ rec_has_key_eq_has_key(recs, kvs, key);
        //@ assert(false == has_key(kvs, key));
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
    //@ rec_get_val_eq_get_val(recs, kvs, key);
    //@ assert(true == rec_has_key(recs, key));
    //@ rec_has_key_eq_has_key(recs, kvs, key);
    //@ assert(true == has_key(kvs, key));
    //@ assert(nth(index, vals) == rec_get_val(recs, key));
    //@ close mapping_(busybits, keys, values, recs);
    //@ close mapping(busybits, keys, values, kvs);
    //@ destroy_bkeys(bks);
    return val;
}

/*@

fixpoint list<kvpair> kv_remove_key(list<kvpair> kvs, int key) {
  switch(kvs) {
    case nil: return nil;
    case cons(h, t):
      return kv_key(h) == key ? kv_remove_key(t, key) : cons(h, kv_remove_key(t, key));
  }
}

lemma void kv_remove_key_preserves_has_not_key(list<kvpair> kvs, int key_rem, int key_abs)
requires false == has_key(kvs, key_abs);
ensures false == has_key(kv_remove_key(kvs, key_rem), key_abs);
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      kv_remove_key_preserves_has_not_key(t, key_rem, key_abs);
      return;
  }
}

lemma void kv_remove_key_preserves_rec_has_key(list<kvpair> kvs, int key_rem, int key)
requires key_rem != key;
ensures has_key(kv_remove_key(kvs, key_rem), key) == has_key(kvs, key);
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      kv_remove_key_preserves_rec_has_key(t, key_rem, key);
      return;
  }
}

lemma void kv_remove_key_preserves_no_dubs(list<kvpair> kvs, int key)
requires true == kv_no_dubs(kvs);
ensures true == kv_no_dubs(kv_remove_key(kvs, key));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      kv_remove_key_preserves_no_dubs(t, key);
      kv_remove_key_preserves_has_not_key(t, key, kv_key(h));
      return;
  }
}

lemma void kv_remove_key_preserves_kvs_contain_rec(list<kvpair> kvs, record rec, int key)
requires true == kvs_contain_rec(kvs, rec) &*& (rec_bb(rec) == 0 || rec_key(rec) != key);
ensures true == kvs_contain_rec(kv_remove_key(kvs, key), rec);
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(rec) != 0) {
        if (kv_key(h) == rec_key(rec)) {
        } else {
          kv_remove_key_preserves_kvs_contain_rec(t, rec, key);
        }
      } else {
        switch(kv_remove_key(kvs, key)) {
          case nil:break;
          case cons(rkh, rkt): break;
        }
      }
      return;
  }
}

lemma void kv_remove_key_preserves_rec2kv_inj(list<record> recs, list<kvpair> kvs, int key)
requires true == forall(recs, (kvs_contain_rec)(kvs)) &*& false == rec_has_key(recs, key);
ensures true == forall(recs, (kvs_contain_rec)(kv_remove_key(kvs, key)));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == key) {
        assert(true == has_key(recs, key));
      } else {
        kv_remove_key_preserves_kvs_contain_rec(kvs, h, key);
        kv_remove_key_preserves_rec2kv_inj(t, kvs, key);
      }
      return;
  }
}

lemma void kv_remove_key_preserves_kv2rec_inj(list<kvpair> kvs, list<record> recs, int key)
requires true == forall(kvs, (recs_contain_kv)(recs));
ensures true == forall(kv_remove_key(kvs, key), (recs_contain_kv)(recs));
{
  switch(kvs){
    case nil: return;
    case cons(h, t):
      kv_remove_key_preserves_kv2rec_inj(t, recs, key);
      if (kv_key(h) == key) {
      } else {
      }
      return;
  }
}

lemma void kv_remove_key_removes_key(list<kvpair> kvs, int key)
requires true;
ensures false == has_key(kv_remove_key(kvs, key), key);
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      kv_remove_key_removes_key(t, key);
      return;
  }
}

lemma void rec_tail_contains_rest(list<kvpair> kvs, list<record> recs, record rec)
requires true == forall(kvs, (recs_contain_kv)(cons(rec, recs))) &*& (false == has_key(kvs, rec_key(rec)) || rec_bb(rec) == 0);
ensures true == forall(kvs, (recs_contain_kv)(recs));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(rec) != 0 && kv_key(h) == rec_key(rec)) {
      } else {
        switch(cons(rec, recs)){
          case nil: break;
          case cons(rech, rect): break;
        }
        rec_tail_contains_rest(t, recs, rec);
      }
      return;
  }
}

lemma void remove_first_key_preserves_mapping(list<kvpair> kvs, record rec, list<record> recs)
requires recs_mapping(cons(rec, recs), kvs) &*& true == no_dubs(cons(rec, recs)) &*& rec_bb(rec) != 0;
ensures recs_mapping(cons(rec, recs), kvs) &*& recs_mapping(recs, kv_remove_key(kvs, rec_key(rec)));
{
  open recs_mapping(cons(rec, recs), kvs);

  kv_remove_key_preserves_no_dubs(kvs, rec_key(rec));
  kv_remove_key_preserves_kv2rec_inj(kvs, cons(rec, recs), rec_key(rec));
  kv_remove_key_removes_key(kvs, rec_key(rec));
  rec_tail_contains_rest(kv_remove_key(kvs, rec_key(rec)), recs, rec);
  kv_remove_key_preserves_rec2kv_inj(recs, kvs, rec_key(rec));

  close recs_mapping(cons(rec, recs), kvs);
  close recs_mapping(recs, kv_remove_key(kvs, rec_key(rec)));
}

lemma void kv_remove_key_not_increase_len(list<kvpair> kvs, int key)
requires true;
ensures length(kv_remove_key(kvs, key)) <= length(kvs);
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      kv_remove_key_not_increase_len(t, key);
      return;
  }
}

lemma void kv_remove_key_decreases_len(list<kvpair> kvs, int key)
requires true == has_key(kvs, key);
ensures length(kv_remove_key(kvs, key)) < length(kvs);
{
  switch(kvs) {
    case nil:
      assert(false == has_key(kvs, key));
      return;
    case cons(h, t):
      if (kv_key(h) == key) {
        kv_remove_key_not_increase_len(t, key);
      } else {
        kv_remove_key_decreases_len(t, key);
      }
      return;
  }
}

lemma void kvs_contain_rec2has_key(list<kvpair> kvs, record rec)
requires true == kvs_contain_rec(kvs, rec) &*& rec_bb(rec) != 0;
ensures true == has_key(kvs, rec_key(rec));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (kv_key(h) == rec_key(rec)) {
      } else {
        kvs_contain_rec2has_key(t, rec);
      }
      return;
  }
}

lemma void small2contains_empty(list<int> bbs, list<kvpair> kvs)
requires recs_mapping(?recs, kvs) &*& records(bbs, ?ks, ?vals, recs) &*& true == no_dubs(recs) &*& length(kvs) < length(bbs);
ensures recs_mapping(recs, kvs) &*& records(bbs, ks, vals, recs) &*& true == contains(bbs, 0);
{
  switch(bbs) {
    case nil:
      length_nonnegative(kvs);
      assert(0 < length(bbs));
      return;
    case cons(h, t):
      if (h != 0) {
        open records(bbs, ks, vals, recs);
        open recs_mapping(recs, kvs);
        assert(recs != nil);
        assert(rec_bb(head(recs)) != 0);
        kvs_contain_rec2has_key(kvs, head(recs));
        kv_remove_key_decreases_len(kvs, rec_key(head(recs)));
        close recs_mapping(recs, kvs);
        remove_first_key_preserves_mapping(kvs, head(recs), tail(recs));
        small2contains_empty(t, kv_remove_key(kvs, rec_key(head(recs))));
        open recs_mapping(tail(recs), kv_remove_key(kvs, rec_key(head(recs))));
        close records(bbs, ks, vals, recs);
        return;
      } else {
        return;
      }
  }
}

lemma void kv_remove_key_abscent_id(list<kvpair> kvs, int key)
requires false == has_key(kvs, key);
ensures kvs == kv_remove_key(kvs, key);
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      assert(kv_key(h) != key);
      kv_remove_key_abscent_id(t, key);
      return;
  }
}

lemma void kv_remove_key_decrements_len(list<kvpair> kvs, int key)
requires true == kv_no_dubs(kvs);
ensures length(kvs) <= length(kv_remove_key(kvs, key)) + 1;
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (kv_key(h) == key) {
        assert(false == has_key(t, key));
        kv_remove_key_abscent_id(t, key);
        assert(length(t) == length(kv_remove_key(t, key)));
        return;
      } else {
        kv_remove_key_decrements_len(t, key);
        return;
      }
  }
}

lemma void remove_key_preserves_len(list<record> recs, int key)
requires true;
ensures length(remove_key(recs, key)) == length(recs);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      remove_key_preserves_len(t, key);
      return;
  }
}

lemma void kv2rec_inj_null(list<kvpair> kvs)
requires true == forall(kvs, (recs_contain_kv)(nil));
ensures kvs == nil;
{
  switch(kvs) {
    case nil: return;
    case cons(h, t): return;
  }
}

lemma void rec_tail_for_empty_head(record rec, list<record> recs, list<kvpair> kvs)
requires true == forall(kvs, (recs_contain_kv)(cons(rec, recs))) &*& rec_bb(rec) == 0;
ensures true == forall(kvs, (recs_contain_kv)(recs));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      rec_tail_for_empty_head(rec, recs, t);
      return;
  }
}

lemma void kv2rec_inj_len_le(list<record> recs, list<kvpair> kvs)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& true == kv_no_dubs(kvs);
ensures length(kvs) <= length(recs);
{
  switch(recs) {
    case nil: 
      kv2rec_inj_null(kvs);
      assert(kvs == nil);
      return;
    case cons(h, t):
      if (rec_bb(h) != 0) {
        kv_remove_key_preserves_kv2rec_inj(kvs, recs, rec_key(h));
        kv_remove_key_removes_key(kvs, rec_key(h));
        rec_tail_contains_rest(kv_remove_key(kvs, rec_key(h)), t, h);
        kv_remove_key_preserves_no_dubs(kvs, rec_key(h));
        kv2rec_inj_len_le(t, kv_remove_key(kvs, rec_key(h)));
        kv_remove_key_decrements_len(kvs, rec_key(h));
      } else {
        rec_tail_for_empty_head(h, t, kvs);
        kv2rec_inj_len_le(t, kvs);
      }
      return;
  }
}

lemma void contains_empty2small(list<int> bbs, list<kvpair> kvs)
requires recs_mapping(?recs, kvs) &*& records(bbs, ?ks, ?vals, recs) &*& true == no_dubs(recs) &*& true == contains(bbs, 0);
ensures recs_mapping(recs, kvs) &*& records(bbs, ks, vals, recs) &*& length(kvs) < length(bbs);
{
  switch(bbs) {
    case nil: return;
    case cons(h, t):
      records_same_length(bbs, ks, vals, recs);
      assert(recs != nil);
      cons_head_tail(recs);
      open records(bbs, ks, vals, recs);
      if (h != 0) {
        assert(rec_bb(head(recs)) != 0);
        remove_first_key_preserves_mapping(kvs, head(recs), tail(recs));
        contains_empty2small(t, kv_remove_key(kvs, rec_key(head(recs))));
        open recs_mapping(recs, kvs);
        kv_remove_key_decrements_len(kvs, rec_key(head(recs)));
        close recs_mapping(recs, kvs);
        open recs_mapping(tail(recs), kv_remove_key(kvs, rec_key(head(recs))));
      } else {
        open recs_mapping(recs, kvs);
        rec_tail_for_empty_head(head(recs), tail(recs), kvs);
        kv2rec_inj_len_le(tail(recs), kvs);
        assert(length(kvs) <= length(tail(recs)));
        assert(length(recs) == length(bbs));
        assert(length(kvs) < length(bbs));
        close recs_mapping(recs, kvs);
     }
     close records(bbs, ks, vals, recs);
     return;
  }
}

lemma void full_size(list<int> bbs, list<kvpair> kvs)
requires recs_mapping(?recs, kvs) &*& records(bbs, ?ks, ?vals, recs) &*& true == no_dubs(recs);
ensures recs_mapping(recs, kvs) &*& records(bbs, ks, vals, recs) &*& contains(bbs, 0) == (length(kvs) < length(bbs));
{
  if (contains(bbs, 0)) {
    contains_empty2small(bbs, kvs);
  } else {
    if (length(kvs) < length(bbs)) {
      small2contains_empty(bbs, kvs);
    } else {
    }
  }
}

lemma void update_key_value_preserve_has_not_key(list<record> recs, int abs_key, int index, int bb, int key, int val)
requires false == rec_has_key(recs, abs_key) &*& (bb == 0 || abs_key != key);
ensures false == rec_has_key(update(index, rec_triple(bb, key, val), recs), abs_key);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        update_key_value_preserve_has_not_key(t, abs_key, index - 1, bb, key, val);
      }
      return;
  }
}

lemma void add_key_value_preserve_no_dubs(list<record> recs, int index, int bb, int key, int val)
requires true == no_dubs(recs) &*& false == rec_has_key(recs, key);
ensures true == no_dubs(update(index, rec_triple(bb, key, val), recs));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        if (rec_bb(h) != 0) {
          update_key_value_preserve_has_not_key(t, rec_key(h), index - 1, bb, key, val);
        } else {
        }
        add_key_value_preserve_no_dubs(t, index - 1, bb, key, val);
      }
      return;
  }
}

lemma void update_recs(list<int> bbs, list<int> ks, list<int> vals, list<record> recs, int index, int nbb, int nk, int nval)
requires records(bbs, ks, vals, recs) &*& 0 <= index;
ensures records(update(index, nbb, bbs), update(index, nk, ks), update(index, nval, vals), update(index, rec_triple(nbb, nk, nval), recs));
{
  open records(bbs, ks, vals, recs);
  switch(recs) {
    case nil: break;
    case cons(h, t):
      cons_head_tail(bbs);
      cons_head_tail(ks);
      cons_head_tail(vals);
      if (index > 0) {
        update_recs(tail(bbs), tail(ks), tail(vals), t, index - 1, nbb, nk, nval);
        update_tail_tail_update(head(bbs), tail(bbs), index, nbb);
        update_tail_tail_update(head(ks), tail(ks), index, nk);
        update_tail_tail_update(head(vals), tail(vals), index, nval); 
      } else {
        assert(index == 0);
        update_0_tail(bbs, nbb);
        update_0_tail(ks, nk);
        update_0_tail(vals, nval);
      }
      break;
  }
  close records(update(index, nbb, bbs), update(index, nk, ks), update(index, nval, vals), update(index, rec_triple(nbb, nk, nval), recs));
}

lemma void insert_rec_preserves_recs_contain_kv(list<record> recs, kvpair kv, int index, int bb, int key, int val)
requires true == recs_contain_kv(recs, kv) &*& 0 <= index &*& index < length(recs) &*& rec_bb(nth(index, recs)) == 0;
ensures true == recs_contain_kv(update(index, rec_triple(bb, key, val), recs), kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index > 0) {
        if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv) && rec_val(h) == kv_value(kv)) {
        } else {
          insert_rec_preserves_recs_contain_kv(t, kv, index - 1, bb, key, val);
          update_tail_tail_update(h, t, index, rec_triple(bb, key, val));
        }
      } else {
        assert(rec_bb(h) == 0);
        assert(true == recs_contain_kv(t, kv));
        update_0_tail(recs, rec_triple(bb, key, val));
      }
      return;
  }
}

lemma void insert_rec_preserves_kv2rec_inj(list<record> recs, list<kvpair> kvs, int index, int bb, int key, int val)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& 0 <= index &*& index < length(recs) &*& rec_bb(nth(index, recs)) == 0;
ensures true == forall(kvs, (recs_contain_kv)(update(index, rec_triple(bb, key, val), recs)));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      insert_rec_preserves_recs_contain_kv(recs, h, index, bb, key, val);
      insert_rec_preserves_kv2rec_inj(recs, t, index, bb, key, val);
      return;
  }
}

lemma void insert_rec_adds_key(list<record> recs, int index, int bb, int key, int val)
requires 0 <= index &*& index < length(recs) &*& bb != 0;
ensures true == recs_contain_kv(update(index, rec_triple(bb, key, val), recs), kvpair_constr(key, val));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        insert_rec_adds_key(t, index - 1, bb, key, val);
        update_tail_tail_update(h, t, index, rec_triple(bb, key, val));
      }
      return;
  }
}

lemma void insert_rec_kv2rec_inj(list<record> recs, list<kvpair> kvs, int index, int bb, int key, int val)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& 0 <= index &*& index < length(recs) &*& bb != 0 &*& rec_bb(nth(index, recs)) == 0;
ensures true == forall(cons(kvpair_constr(key, val), kvs), (recs_contain_kv)(update(index, rec_triple(bb, key, val), recs)));
{
  insert_rec_preserves_kv2rec_inj(recs, kvs, index, bb, key, val);
  insert_rec_adds_key(recs, index, bb, key, val);
}

lemma void kv_cons_preserves_rec2kv_inj(list<record> recs, list<kvpair> kvs, kvpair extra)
requires true == forall(recs, (kvs_contain_rec)(kvs)) &*& false == rec_has_key(recs, kv_key(extra));
ensures true == forall(recs, (kvs_contain_rec)(cons(extra, kvs)));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      kv_cons_preserves_rec2kv_inj(t, kvs, extra);
      return;
  }
}

lemma void insert_rec_rec2kv_inj(list<record> recs, list<kvpair> kvs, int index, int bb, int key, int val)
requires true == forall(recs, (kvs_contain_rec)(kvs)) &*& 0 <= index &*& index < length(recs) &*& false == rec_has_key(recs, key);
ensures true == forall(update(index, rec_triple(bb, key, val), recs), (kvs_contain_rec)(cons(kvpair_constr(key, val), kvs)));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
        kv_cons_preserves_rec2kv_inj(t, kvs, kvpair_constr(key, val));
      } else {
        insert_rec_rec2kv_inj(t, kvs, index - 1, bb, key, val);
        update_tail_tail_update(h, t, index, rec_triple(bb, key, val));
      }
      return;
  }
}

lemma void insert_mapping(list<record> recs, list<kvpair> kvs, int index, int bb, int key, int val)
requires recs_mapping(recs, kvs) &*& false == has_key(kvs, key) &*& 0 <= index &*& index < length(recs) &*& bb != 0 &*& rec_bb(nth(index, recs)) == 0 &*& true == no_dubs(recs) &*& false == rec_has_key(recs, key);
ensures recs_mapping(update(index, rec_triple(bb, key, val), recs), cons(kvpair_constr(key, val), kvs));
{
  open recs_mapping(recs, kvs);
  
  insert_rec_kv2rec_inj(recs, kvs, index, bb, key, val);
  insert_rec_rec2kv_inj(recs, kvs, index, bb, key, val);

  close recs_mapping(update(index, rec_triple(bb, key, val), recs), cons(kvpair_constr(key, val), kvs));
}

@*/

int put(int* busybits, int* keys, int* values, int key, int value)
//@ requires mapping(busybits, keys, values, ?kvs) &*& false == has_key(kvs, key);
//@ ensures length(kvs) < CAPACITY ? mapping(busybits, keys, values, cons(kvpair_constr(key, value), kvs)) &*& result == 0 \
                                   : mapping(busybits, keys, values, kvs) &*& result == -1;
{
    //@ open mapping(busybits, keys, values, kvs);
    //@ open mapping_(busybits, keys, values, ?recs);
    //@ assert records(?bbs, ?ks, ?vals, recs);
    //@ full_size(bbs, kvs);
    //@ records_same_length(bbs, ks, vals, recs);
    int start = loop(key);
    int index = find_empty(busybits, start);

    if (-1 == index)
    {
        //@ assert(length(bbs) == CAPACITY);
        //@ assert(CAPACITY <= length(kvs));
        //@ close mapping_(busybits, keys, values, recs);
        //@ close mapping(busybits, keys, values, kvs);
        return -1;
    }
    //@ assert(length(recs) == CAPACITY);
    //@ nth_bbs_keys_vals_recs(index, bbs, ks, vals, recs);
    busybits[index] = 1;
    keys[index] = key;
    values[index] = value;
    //@ update_recs(bbs, ks, vals, recs, index, 1, key, value);
    //@ rec_has_key_eq_has_key(recs, kvs, key);
    //@ insert_mapping(recs, kvs, index, 1, key, value);
    //@ add_key_value_preserve_no_dubs(recs, index, 1, key, value);
    //@ assert(length(kvs) < CAPACITY);
    //@ close mapping_(busybits, keys, values, update(index, rec_triple(1, key, value), recs));
    //@ close mapping(busybits, keys, values, cons(kvpair_constr(key, value), kvs));
    return 0;
}

/*@
fixpoint list<kvpair> rem_key(list<kvpair> kvs, int key) {
  switch(kvs) {
    case nil: return nil;
    case cons(h, t):
      return kv_key(h) == key ? rem_key(t, key) : cons(h, rem_key(t, key));
  }
}

lemma void kv_remove_key_value_preserve_no_dubs(list<record> recs, int index, int key, int val)
requires true == no_dubs(recs);
ensures true == no_dubs(update(index, rec_triple(0, key, val), recs));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        if (rec_bb(h) != 0) {
          update_key_value_preserve_has_not_key(t, rec_key(h), index - 1, 0, key, val);
        } else {
        }
        kv_remove_key_value_preserve_no_dubs(t, index - 1, key, val);
      }
      return;
  }
}

lemma void rec_cons_preserves_kv2rec_inj(list<kvpair> kvs, list<record> recs, record extra)
requires true == forall(kvs, (recs_contain_kv)(recs));
ensures true == forall(kvs, (recs_contain_kv)(cons(extra, recs)));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      rec_cons_preserves_kv2rec_inj(t, recs, extra);
      return;
  }
}

lemma void remove_key_tidy(list<record> recs, int index, int key)
requires rec_key(nth(index, recs)) != key;
ensures nth(index, recs) == nth(index, remove_key(recs, key));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        remove_key_tidy(t, index - 1, key);
      }
      return;
  }
}

lemma void rem_rec_abscent_preserves_recs_contain_kv(list<record> recs, kvpair kv, int index, int key, int val)
requires true == recs_contain_kv(recs, kv) &*& kv_key(kv) != rec_key(nth(index, recs));
ensures true == recs_contain_kv(update(index, rec_triple(0, key, val), recs), kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv) && rec_val(h) == kv_value(kv)) {
        } else {
          rem_rec_abscent_preserves_recs_contain_kv(t, kv, index - 1, key, val);
        }
      }
      return;
  }
}

lemma void rem_rec_abscent_preserves_kv2rec_inj(list<record> recs, list<kvpair> kvs, int index, int key, int val)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& false == has_key(kvs, rec_key(nth(index, recs)));
ensures true == forall(kvs, (recs_contain_kv)(update(index, rec_triple(0, key, val), recs)));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      rem_rec_abscent_preserves_kv2rec_inj(recs, t, index, key, val);
      rem_rec_abscent_preserves_recs_contain_kv(recs, h, index, key, val);
      return;
  }
}

lemma void rem_rec_preserves_recs_contain_kv(list<record> recs, kvpair kv, int index, int key, int val)
requires true == recs_contain_kv(recs, kv) &*& kv_key(kv) != rec_key(nth(index, recs));
ensures true == recs_contain_kv(update(index, rec_triple(0, key, val), recs), kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
        assert(rec_key(h) != kv_key(kv));
        assert(true == recs_contain_kv(t, kv));
      } else {
        if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv) && rec_val(h) == kv_value(kv)) {
        } else {
          rem_rec_preserves_recs_contain_kv(t, kv, index - 1, key, val);
        }
      }
      return;
  }
}

lemma void update_remove_key_comm(list<record> recs, int rem_key, int index, int key, int val)
requires true;
ensures update(index, rec_triple(0, key, val), remove_key(recs, rem_key)) ==
        remove_key(update(index, rec_triple(0, key, val), recs), rem_key);
{
  switch(recs) { 
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        update_remove_key_comm(t, rem_key, index - 1, key, val);
      }
      return;
  }
}

lemma void unremove_key_preserves_recs_contain_kv(list<record> recs, kvpair kv, int key)
requires true == recs_contain_kv(remove_key(recs, key), kv);
ensures true == recs_contain_kv(recs, kv);
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (rec_bb(h) != 0 && rec_key(h) == kv_key(kv) && rec_val(h) == kv_value(kv)) {
      } else {
        unremove_key_preserves_recs_contain_kv(t, kv, key);
      }
      return;
  }
}

lemma void unremove_key_preserves_kv2rec_inj(list<kvpair> kvs, list<record> recs, int key)
requires true == forall(kvs, (recs_contain_kv)(remove_key(recs, key)));
ensures true == forall(kvs, (recs_contain_kv)(recs));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      unremove_key_preserves_kv2rec_inj(t, recs, key);
      unremove_key_preserves_recs_contain_kv(recs, h, key);
      return;
  }
}

lemma void rem_rec_kv2rec_inj(list<record> recs, list<kvpair> kvs, int index, int key, int val)
requires true == forall(kvs, (recs_contain_kv)(recs)) &*& 0 <= index &*& index < length(recs) &*& rec_bb(nth(index, recs)) != 0 &*& true == no_dubs(recs) &*& true == kv_no_dubs(kvs);
ensures true == forall(kv_remove_key(kvs, rec_key(nth(index, recs))), (recs_contain_kv)(update(index, rec_triple(0, key, val), recs)));
{
  switch(kvs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
        if (recs == nil) return;
        cons_head_tail(recs);
        kv_remove_key_preserves_kv2rec_inj(kvs, recs, rec_key(head(recs)));
        kv_remove_key_removes_key(kvs, rec_key(head(recs)));
        rec_tail_contains_rest(kv_remove_key(kvs, rec_key(head(recs))), tail(recs), head(recs));
        update_0_tail(recs, rec_triple(0, key, val));
        rec_cons_preserves_kv2rec_inj(kv_remove_key(kvs, rec_key(head(recs))), tail(recs), rec_triple(0, key, val));
      } else {
        if (kv_key(h) == rec_key(nth(index, recs))) {
          assert(kv_remove_key(kvs, rec_key(nth(index, recs))) == kv_remove_key(t, rec_key(nth(index, recs))));
          kv_remove_key_abscent_id(t, kv_key(h));
          assert(kv_remove_key(t, kv_key(h)) == t);
          rem_rec_abscent_preserves_kv2rec_inj(recs, t, index, key, val);
        } else {
          remove_key_preserves_no_dubs(recs, kv_key(h));
          remove_key_preserves_kv2rec_inj(t, recs, kv_key(h));
          remove_key_preserves_len(recs, kv_key(h));
          remove_key_tidy(recs, index, kv_key(h));
          rem_rec_kv2rec_inj(remove_key(recs, kv_key(h)), t, index, key, val);
          rem_rec_preserves_recs_contain_kv(recs, h, index, key, val);
          update_remove_key_comm(recs, kv_key(h), index, key, val);
          unremove_key_preserves_kv2rec_inj(kv_remove_key(t, rec_key(nth(index, recs))),
                                            update(index, rec_triple(0, key, val), recs),
                                            kv_key(h));
        }
      }
      return;
  }
}

lemma void rec_has_key_not_ith_key_matches_not(list<record> recs, int index, int key)
requires false == rec_has_key(recs, key) &*& rec_bb(nth(index, recs)) != 0 &*& 0 <= index &*& index < length(recs);
ensures rec_key(nth(index, recs)) != key;
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
      } else {
        rec_has_key_not_ith_key_matches_not(t, index - 1, key);
      }
      return;
  }
}

lemma void rem_rec_rec2kv_inj(list<record> recs, list<kvpair> kvs, int index, int key, int val)
requires true == forall(recs, (kvs_contain_rec)(kvs)) &*& 0 <= index &*& index < length(recs) &*& rec_bb(nth(index, recs)) != 0 &*& true == no_dubs(recs);
ensures true == forall(update(index, rec_triple(0, key, val), recs), (kvs_contain_rec)(kv_remove_key(kvs, rec_key(nth(index, recs)))));
{
  switch(recs) {
    case nil: return;
    case cons(h, t):
      if (index == 0) {
        kv_remove_key_preserves_rec2kv_inj(t, kvs, rec_key(h));
        switch(kv_remove_key(kvs, rec_key(h))){
          case nil: break;
          case cons(kvh, kvt): break;
        }
        assert(true == kvs_contain_rec(kv_remove_key(kvs, rec_key(h)), rec_triple(0, key, val)));
      } else {
        rem_rec_rec2kv_inj(t, kvs, index - 1, key, val);
        assert(true == kvs_contain_rec(kvs, h));
        if (rec_bb(h) != 0) {
          rec_has_key_not_ith_key_matches_not(t, index - 1, rec_key(h));
        }
        kv_remove_key_preserves_kvs_contain_rec(kvs, h, rec_key(nth(index, recs)));
        assert(true == kvs_contain_rec(kv_remove_key(kvs, rec_key(nth(index, recs))), h));
      }
      return;
  }
}

lemma void remove_mapping(list<record> recs, list<kvpair> kvs, int index, int key, int val)
requires recs_mapping(recs, kvs) &*& 0 <= index &*& index < length(recs) &*& rec_bb(nth(index, recs)) != 0 &*& true == no_dubs(recs);
ensures recs_mapping(update(index, rec_triple(0, key, val), recs), kv_remove_key(kvs, rec_key(nth(index, recs))));
{
  open recs_mapping(recs, kvs);

  rem_rec_kv2rec_inj(recs, kvs, index, key, val);
  rem_rec_rec2kv_inj(recs, kvs, index, key, val);
  kv_remove_key_preserves_no_dubs(kvs, rec_key(nth(index, recs)));

  close recs_mapping(update(index, rec_triple(0, key, val), recs), kv_remove_key(kvs, rec_key(nth(index, recs))));
}

@*/

int erase(int* busybits, int* keys, int key)
//@ requires mapping(busybits, keys, ?values, ?kvs);
//@ ensures has_key(kvs, key) ? mapping(busybits, keys, values, kv_remove_key(kvs, key)) &*& result == 0 \
    : mapping(busybits, keys, values, kvs) &*& result == -1;
{
    //@ open mapping(busybits, keys, values, kvs);
    //@ open mapping_(busybits, keys, values, ?recs);
    //@ assert records(?bbs, ?ks, ?vals, recs);
    //@ list<busy_key> bks = make_bkeys_from_recs(bbs, ks, vals, recs);
    int start = loop(key);
    int index = find_key(busybits, keys, start, key);
    //@ bkhas_key2rec_has_key(recs, bks, key);
    //@ rec_has_key_eq_has_key(recs, kvs, key);
    //@ records_same_length(bbs, ks, vals, recs);
    //@ bkeys_len_eq(bks, bbs, ks);

    if (-1 == index)
    {
        //@ assert(false == has_key(kvs, key));
        //@ close mapping_(busybits, keys, values, recs);
        //@ close mapping(busybits, keys, values, kvs);
        //@ destroy_bkeys(bks);
        return -1;
    }
    //@ assert(true == has_key(kvs, key));
    busybits[index] = 0;
    //@ update_id(index, ks);
    //@ update_id(index, vals);
    //@ nth_bbs_keys_vals_recs(index, bbs, ks, vals, recs);
    //@ nth_bbs_keys_bkeys(index, bbs, ks, bks);
    //@ update_recs(bbs, ks, vals, recs, index, 0, nth(index, ks), nth(index, vals));
    //@ kv_remove_key_value_preserve_no_dubs(recs, index, nth(index, ks), nth(index, vals));
    //@ close mapping_(busybits, keys, values, update(index, rec_triple(0, nth(index, ks), nth(index, vals)), recs));
    //@ remove_mapping(recs, kvs, index, nth(index, ks), nth(index, vals));
    //@ close mapping(busybits, keys, values, kv_remove_key(kvs, key));
    //@ destroy_bkeys(bks);
    return 0;
}

/*@
fixpoint int busy_len(list<int> bbs) {
  switch(bbs) {
    case nil: return 0;
    case cons(h, t):
      return (h != 0 ? 1 : 0) + busy_len(t);
  }
}

lemma void busy_len_add_bit(list<int> bbs, int i, int s)
requires s == busy_len(take(i, bbs)) &*& 0 <= i &*& i < length(bbs);
ensures nth(i, bbs) != 0 ? s + 1 == busy_len(take(i + 1, bbs)) : s == busy_len(take(i + 1, bbs));
{
  switch(bbs) {
    case nil: return;
    case cons(h, t):
      if (i == 0) {
      } else {
        if (h != 0) {
          busy_len_add_bit(t, i - 1, s - 1);
        } else {
          busy_len_add_bit(t, i - 1, s);
        }
      }
      return;
  }
}

fixpoint int rec_busy_len(list<record> recs) {
  switch(recs) {
    case nil: return 0;
    case cons(h, t):
      return (rec_bb(h) != 0 ? 1 : 0) + rec_busy_len(t);
  }
}

lemma void busy_len2rec_busy_len(list<int> bbs, list<record> recs)
requires records(bbs, ?ks, ?vals, recs);
ensures records(bbs, ks, vals, recs) &*& busy_len(bbs) == rec_busy_len(recs);
{
  open records(bbs, ks, vals, recs);
  switch(recs) {
    case nil: break;
    case cons(h, t):
      cons_head_tail(bbs);
      busy_len2rec_busy_len(tail(bbs), t);
      break;
  }
  close records(bbs, ks, vals, recs);
}

lemma void rec_busy_len_is_the_size(list<record> recs, list<kvpair> kvs)
requires recs_mapping(recs, kvs) &*& true == no_dubs(recs);
ensures recs_mapping(recs, kvs) &*& rec_busy_len(recs) == length(kvs);
{
  switch(recs) {
    case nil:
      open recs_mapping(recs, kvs);
      close recs_mapping(recs, kvs);
      kv2rec_inj_null(kvs);
      break;
    case cons(h, t):
      open recs_mapping(recs, kvs);
      close recs_mapping(recs, kvs);
      if (rec_bb(h) != 0) {
        remove_first_key_preserves_mapping(kvs, h, t);
        kvs_contain_rec2has_key(kvs, h);
        kv_remove_key_decreases_len(kvs, rec_key(h));
        kv_remove_key_decrements_len(kvs, rec_key(h));
        rec_busy_len_is_the_size(t, kv_remove_key(kvs, rec_key(h)));
        open recs_mapping(t, kv_remove_key(kvs, rec_key(h)));
      } else {
        rec_tail_contains_rest(kvs, t, h);
        close recs_mapping(t, kvs);
        rec_busy_len_is_the_size(t, kvs);
        open recs_mapping(t, kvs);
      }
      break;
  }
}

@*/


int size(int* busybits)
//@ requires mapping(busybits, ?keys, ?values, ?kvs);
//@ ensures mapping(busybits, keys, values, kvs) &*& result == length(kvs);
{
    int s = 0;
    //@ open mapping(busybits, keys, values, kvs);
    //@ open mapping_(busybits, keys, values, ?recs);
    //@ assert records(?bbs, ?ks, ?vals, recs);
    for (int i = 0; i < CAPACITY; ++i)
        /*@ invariant s == busy_len(take(i, bbs)) &*& 0 <= i &*& i <= CAPACITY &*&
          ints(busybits, CAPACITY, bbs) &*& records(bbs, ks, vals, recs) &*& s <= i; @*/
    {
        //@ busy_len_add_bit(bbs, i, s);
        if (busybits[i] != 0)
        {
            ++s;
        }
    }
    //@ assert(s == busy_len(bbs));
    //@ busy_len2rec_busy_len(bbs, recs);
    //@ assert(s == rec_busy_len(recs));
    //@ rec_busy_len_is_the_size(recs, kvs);
    //@ close mapping_(busybits, keys, values, recs);
    //@ close mapping(busybits, keys, values, kvs);
    return s;
}
