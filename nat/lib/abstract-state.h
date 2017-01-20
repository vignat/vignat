#include "containers/double-map.h"
#include "containers/double-chain.h"
#include "flow.h"
#include "coherence.h"

/*@

inductive entry = entry(int_k, ext_k, flw, uint32_t tstmp);
inductive flowtable = flowtable(int, list<entry>);

fixpoint int_k entry_ik(entry e) {
  switch(e) { case entry(ik, ek, flw, tstmp):
    return ik;
  }
}

fixpoint ext_k entry_ek(entry e) {
  switch(e) { case entry(ik, ek, flw, tstmp):
    return ek;
  }
}
fixpoint flw entry_flow(entry e) {
  switch(e) { case entry(ik, ek, flw, tstmp):
    return flw;
  }
}

fixpoint uint32_t entry_tstamp(entry e) {
  switch(e) { case entry(ik, ek, flw, tstmp):
    return tstmp;
  }
}

fixpoint t alist_get_by_right<t>(list<pair<t, int> > alist, int idx) {
  switch(alist) {
    case nil: return default_value<t>();
    case cons(h,t): return switch(h) { case pair(x, i):
      return (i == idx) ? x : alist_get_by_right(t, idx);
    };
  }
}

fixpoint list<entry> gen_entries(list<pair<int, uint32_t> > indices,
                                 list<pair<int_k, int> > ikeys,
                                 list<pair<ext_k, int> > ekeys,
                                 list<option<flw> > flows) {
  switch(indices) {
    case nil: return nil;
    case cons(h,t): return switch(h) { case pair(index, tstmp):
      return cons(entry(alist_get_by_right(ikeys, index),
                        alist_get_by_right(ekeys, index),
                        get_some(nth(index, flows)),
                        tstmp),
                  gen_entries(t, ikeys, ekeys, flows));
    };
  }
}

fixpoint flowtable abstract_function(dmap<int_k,ext_k,flw> m, dchain ch) {
  switch(ch) { case dchain(entries, index_range, low, high):
    return switch(m) { case dmap(ikeys, ekeys, vals) :
      return flowtable(index_range, gen_entries(entries, ikeys, ekeys, vals));
    };
  }
}

fixpoint bool flowtable_contains_int_flow_id(flowtable ft, int_k flow_id) {
  switch(ft) { case flowtable(size, entries):
    return mem(flow_id, map(entry_ik, entries));
  }
}

fixpoint bool flowtable_contains_ext_flow_id(flowtable ft, ext_k flow_id) {
  switch(ft) { case flowtable(size, entries):
    return mem(flow_id, map(entry_ek, entries));
  }
}

fixpoint flw flowtable_get_by_int_flow_id(flowtable ft, int_k flow_id) {
  switch(ft) { case flowtable(size, entries):
    return entry_flow(nth(index_of(flow_id, map(entry_ik, entries)), entries));
  }
}

fixpoint flw flowtable_get_by_ext_flow_id(flowtable ft, ext_k flow_id) {
  switch(ft) { case flowtable(size, entries):
    return entry_flow(nth(index_of(flow_id, map(entry_ek, entries)), entries));
  }
}

fixpoint bool flowtable_out_of_space(flowtable ft) {
  switch(ft) { case flowtable(size, entries):
    return size <= length(entries);
  }
}

fixpoint list<t> remove_if<t>(fixpoint (t,bool) cond, list<t> l) {
  switch(l) {
    case nil: return nil;
    case cons(h,t):
      return cond(h)? t : cons(h, remove_if(cond, t));
  }
}

fixpoint bool entry_matches_flow(flw f, entry e) {
  return entry_flow(e) == f;
}

fixpoint flowtable flowtable_add_flow(flowtable table, flw flow, uint32_t time) {
  switch(table) { case flowtable(size, entries):
    return flowtable(size, append(entries,
                                  cons(entry(flw_get_ik(flow),
                                             flw_get_ek(flow),
                                             flow,
                                             time),
                                       nil)));
  }
}

fixpoint flowtable flowtable_remove_flow(flowtable table, flw flow) {
  switch(table) { case flowtable(size, entries):
    return flowtable(size, remove_if((entry_matches_flow)(flow), entries));
  }
}

fixpoint list<entry> expire_entries(list<entry> entries, uint32_t time) {
  switch(entries) {
    case nil: return nil;
    case cons(h,t): return entry_tstamp(h) < time           ?
                           expire_entries(t, time)          :
                           cons(h, expire_entries(t, time));
  }
}

fixpoint flowtable flowtable_expire_flows(flowtable table, uint32_t time) {
  switch(table) { case flowtable(size, entries):
    return flowtable(size, expire_entries(entries, time));
  }
}

fixpoint list<entry> expire_n_entries(list<entry> entries, uint32_t time,
                                      int to_expire) {
  switch(entries) {
    case nil: return nil;
    case cons(h,t):
      return (to_expire <= 0) ?
                  entries :
                  (entry_tstamp(h) < time ?
                   expire_n_entries(t, time, to_expire - 1)      :
                   cons(h, expire_n_entries(t, time, to_expire)));
  }
}

fixpoint flowtable flowtable_expire_n_flows(flowtable table, uint32_t time,
                                            int count) {
  switch(table) { case flowtable(size, entries):
    return flowtable(size, expire_n_entries(entries, time, count));
  }
}
@*/


/*@
  lemma void dchain_allocated_mem_map(list<pair<int, uint32_t> > entries,
                                      int index_range, int low, int high,
                                      int index)
  requires true;
  ensures dchain_allocated_fp(dchain(entries, index_range, low, high), index) ==
          mem(index, map(fst, entries));
  {
    switch(entries) {
      case nil:
      case cons(h,t): switch(h) { case pair(ind,tstmp):
        if (ind != index) dchain_allocated_mem_map(t, index_range, low,
                                                   high, index);
      }
    }
  }
  @*/


/*@
  lemma void gen_entries_has_ik_ek_flow_by_index
    (list<pair<int, uint32_t> > entries,
     list<pair<int_k, int> > ikeys,
     list<pair<ext_k, int> > ekeys,
     list<option<flw> > vals,
     int index)
  requires true == mem(index, map(fst, entries));
  ensures true == mem(alist_get_by_right(ekeys, index),
                      map(entry_ek, gen_entries(entries, ikeys, ekeys, vals))) &*&
          true == mem(alist_get_by_right(ikeys, index),
                      map(entry_ik, gen_entries(entries, ikeys, ekeys, vals))) &*&
          true == mem(get_some(nth(index, vals)),
                      map(entry_flow, gen_entries(entries, ikeys, ekeys, vals)));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          if (ind != index) {
            gen_entries_has_ik_ek_flow_by_index(t, ikeys, ekeys, vals, index);
          }
        }
    }
  }
  @*/


/*@
  lemma void alist_get_by_right_map_get<kt>(list<pair<kt, int> > m,
                                            kt k)
  requires true == map_has_fp(m, k) &*&
           true == no_dups(map(snd, m));
  ensures k == alist_get_by_right(m, map_get_fp(m, k)) &*&
          true == mem(map_get_fp(m, k), map(snd, m));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) {
            alist_get_by_right_map_get(t, k);
          }
        }
    }
  }
  @*/

/*@
  lemma void abscent_key_alist_wont_give<kt>(list<pair<kt, int> > m, kt k, int i)
  requires false == mem(k, map(fst, m)) &*&
           true == mem(i, map(snd, m));
  ensures alist_get_by_right(m, i) != k;
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (i != ind) abscent_key_alist_wont_give(t, k, i);
        }
    }
  }
  @*/


/*@
  lemma void gen_entries_also_no_ek(list<pair<int, uint32_t> > entries,
                                    list<pair<int_k, int> > ikeys,
                                    list<pair<ext_k, int> > ekeys,
                                    list<option<flw> > vals,
                                    ext_k ek)
  requires false == mem(ek, map(fst, ekeys)) &*&
           true == forall(map(fst, entries), (contains)(map(snd, ekeys)));
  ensures false == mem(ek, map(entry_ek,
                               gen_entries(entries, ikeys, ekeys, vals)));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          abscent_key_alist_wont_give(ekeys, ek, ind);
          gen_entries_also_no_ek(t, ikeys, ekeys, vals, ek);
        }
    }
  }
  @*/


/*@
// Head lemma #
lemma void contains_ext_k_abstract(dmap<int_k,ext_k,flw> m, dchain ch,
                                   ext_k ek)
requires dmap_dchain_coherent(m, ch) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  vk1, vk2, recp1, recp2, mp) &*&
        flowtable_contains_ext_flow_id(abstract_function(m, ch), ek) ==
        dmap_has_k2_fp(m, ek);
{
  if (dmap_has_k2_fp(m, ek)) {
    int index = dmap_get_k2_fp(m, ek);
    dmap_get_k2_limits(m, ek);
    assert true == dmap_index_used_fp(m, index);
    coherent_dmap_used_dchain_allocated(m, ch, index);
    assert true == dchain_allocated_fp(ch, index);
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        dchain_allocated_mem_map(entries, index_range, low, high, index);
        assert true == mem(index, map(fst, entries));
        gen_entries_has_ik_ek_flow_by_index(entries, ikeys, ekeys, vals, index);
        dmap_indices_no_dups(ikeys, ekeys, vals);
        alist_get_by_right_map_get(ekeys, ek);
        assert ek == alist_get_by_right(ekeys, index);
        assert true == mem(ek, map(entry_ek, gen_entries(entries, ikeys, ekeys, vals)));
      }
    }
  } else {
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        map_has_to_mem(ekeys, ek);
        assert false == mem(ek, map(fst, ekeys));
        dmap_indexes_used_used_in_ma_mb(ikeys, ekeys, vals);
        coherent_same_indexes(m, ch);
        assert dchain_indexes_fp(ch) == map(fst, entries);
        subset_forall(map(fst, entries), dmap_indexes_used_fp(m),
                      (contains)(map(snd, ekeys)));
        gen_entries_also_no_ek(entries, ikeys, ekeys, vals, ek);
      }
    }
  }
}
@*/

/*@
  lemma void gen_entries_also_no_ik(list<pair<int, uint32_t> > entries,
                                    list<pair<int_k, int> > ikeys,
                                    list<pair<ext_k, int> > ekeys,
                                    list<option<flw> > vals,
                                    int_k ik)
  requires false == mem(ik, map(fst, ikeys)) &*&
           true == forall(map(fst, entries), (contains)(map(snd, ikeys)));
  ensures false == mem(ik, map(entry_ik,
                               gen_entries(entries, ikeys, ekeys, vals)));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          abscent_key_alist_wont_give(ikeys, ik, ind);
          gen_entries_also_no_ik(t, ikeys, ekeys, vals, ik);
        }
    }
  }
  @*/

/*@
// Head lemma #
lemma void contains_int_k_abstract(dmap<int_k,ext_k,flw> m, dchain ch,
                                   int_k ik)
requires dmap_dchain_coherent(m, ch) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  vk1, vk2, recp1, recp2, mp) &*&
        flowtable_contains_int_flow_id(abstract_function(m, ch), ik) ==
        dmap_has_k1_fp(m, ik);
{
  if (dmap_has_k1_fp(m, ik)) {
    int index = dmap_get_k1_fp(m, ik);
    dmap_get_k1_limits(m, ik);
    assert true == dmap_index_used_fp(m, index);
    coherent_dmap_used_dchain_allocated(m, ch, index);
    assert true == dchain_allocated_fp(ch, index);
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        dchain_allocated_mem_map(entries, index_range, low, high, index);
        assert true == mem(index, map(fst, entries));
        gen_entries_has_ik_ek_flow_by_index(entries, ikeys, ekeys, vals, index);
        dmap_indices_no_dups(ikeys, ekeys, vals);
        alist_get_by_right_map_get(ikeys, ik);
        assert ik == alist_get_by_right(ikeys, index);
        assert true == mem(ik, map(entry_ik, gen_entries(entries, ikeys, ekeys, vals)));
      }
    }
  } else {
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        map_has_to_mem(ikeys, ik);
        assert false == mem(ik, map(fst, ikeys));
        dmap_indexes_used_used_in_ma_mb(ikeys, ekeys, vals);
        coherent_same_indexes(m, ch);
        assert dchain_indexes_fp(ch) == map(fst, entries);
        subset_forall(map(fst, entries), dmap_indexes_used_fp(m),
                      (contains)(map(snd, ikeys)));
        gen_entries_also_no_ik(entries, ikeys, ekeys, vals, ik);
      }
    }
  }
}
@*/


/*@
  lemma void gen_entries_same_len(list<pair<int, uint32_t> > entries,
                                  list<pair<int_k,int> > ikeys,
                                  list<pair<ext_k,int> > ekeys,
                                  list<option<flw> > vals)
  requires true;
  ensures length(entries) == length(gen_entries(entries, ikeys, ekeys, vals));
  {
    switch(entries) {
      case nil:
      case cons(h,t): switch(h) { case pair(index, tstmp):
        gen_entries_same_len(t, ikeys, ekeys, vals);
      }
    }
  }
  @*/


/*@
// Head lemma #
lemma void out_of_space_abstract(dmap<int_k,ext_k,flw> m, dchain ch)
requires true;
ensures flowtable_out_of_space(abstract_function(m, ch)) ==
        dchain_out_of_space_fp(ch);
{
  switch(ch) { case dchain(entries, index_range, low, high):
    switch(m) { case dmap(ikeys, ekeys, vals):
      gen_entries_same_len(entries, ikeys, ekeys, vals);
    }
  }
}
@*/

/*@
  lemma void gen_entries_add_flow(list<pair<int, uint32_t> > entries,
                                  list<pair<int_k,int> > ikeys,
                                  list<pair<ext_k,int> > ekeys,
                                  list<option<flw> > vals,
                                  int index,
                                  flw flow,
                                  uint32_t time)
  requires false == exists(entries, (same_index)(index))&*&
           false == map_has_fp(ikeys, flw_get_ik(flow)) &*&
           false == map_has_fp(ekeys, flw_get_ek(flow)) &*&
           false == mem(index, map(snd, ikeys)) &*&
           false == mem(index, map(snd, ekeys)) &*&
           nth(index, vals) == none &*&
           0 <= index &*& index < length(vals) &*&
           true == forall(map(fst, entries), (ge)(0)) &*&
           true == forall(map(fst, entries), (lt)(length(vals)));
  ensures append(gen_entries(entries, ikeys, ekeys, vals),
                 cons(entry(flw_get_ik(flow),
                            flw_get_ek(flow),
                            flow, time),
                      nil)) ==
          gen_entries(append(entries, cons(pair(index, time), nil)),
                      map_put_fp(ikeys, flw_get_ik(flow), index),
                      map_put_fp(ekeys, flw_get_ek(flow), index),
                      update(index, some(flow), vals));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          gen_entries_add_flow(t, ikeys, ekeys, vals, index, flow, time);
          assert alist_get_by_right(ikeys, ind) ==
                 alist_get_by_right(map_put_fp(ikeys, flw_get_ik(flow), index),
                                    ind);
          assert get_some(nth(ind, vals)) == get_some(nth(ind, update(index, some(flow), vals)));
        }
    }
  }
  @*/

/*@
  lemma void index_used_nonnone<t1,t2,vt>(list<pair<t1, int> > ikeys,
                                          list<pair<t2, int> > ekeys,
                                          list<option<vt> > vals,
                                          int index)
  requires 0 <= index &*& index < length(vals);
  ensures dmap_index_used_fp(dmap(ikeys, ekeys, vals), index) ==
          (nth(index, vals) != none);
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        if (0 < index) index_used_nonnone(ikeys, ekeys, t, index - 1);
    }
  }
  @*/


/*@
// Head lemma #
lemma void add_flow_abstract(dmap<int_k,ext_k,flw> m, dchain ch, flw flow,
                             int index, uint32_t t)
requires false == dchain_out_of_space_fp(ch) &*&
         false == dchain_allocated_fp(ch, index) &*&
         dmap_dchain_coherent(m, ch) &*&
         false == dmap_has_k1_fp(m, flw_get_ik(flow)) &*&
         false == dmap_has_k2_fp(m, flw_get_ek(flow)) &*&
         0 <= index &*& index < dchain_index_range_fp(ch) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  vk1, vk2, recp1, recp2, mp) &*&
        flowtable_add_flow(abstract_function(m, ch), flow, t) ==
        abstract_function(dmap_put_fp(m, index, flow, flw_get_ik, flw_get_ek),
                          dchain_allocate_fp(ch, index, t));
{
  switch(ch) { case dchain(entries, index_range, low, high):
    switch(m) { case dmap(ikeys, ekeys, vals):
      if (dmap_index_used_fp(m, index)) {
        coherent_dmap_used_dchain_allocated(m, ch, index);
        assert false;
      }
      coherent_same_cap(m, ch);
      index_used_nonnone(ikeys, ekeys, vals, index);
      dmap_nonnone_index_in_ma_mb(ikeys, ekeys, vals, index);
      nonempty_indexes_bounds(vals, 0);
      assert true == forall(dmap_indexes_used_fp(m), (ge)(0));
      assert true == forall(dmap_indexes_used_fp(m), (lt)(length(vals)));
      coherent_same_indexes(m, ch);
      subset_forall(map(fst, entries), dmap_indexes_used_fp(m), (ge)(0));
      subset_forall(map(fst, entries), dmap_indexes_used_fp(m),
                    (lt)(length(vals)));
      gen_entries_add_flow(entries, ikeys, ekeys, vals,index, flow, t);
    }
  }
}
@*/


/*@
  lemma void map_has_mem_pair<kt>(list<pair<kt, int> > m, kt k)
  requires true == map_has_fp(m, k);
  ensures true == mem(pair(k, map_get_fp(m, k)), m);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) map_has_mem_pair(t, k);
        }
    }
  }
  @*/

/*@
  lemma void map_has_get_by_right<kt>(list<pair<kt, int> > m, kt k, int i)
  requires true == mem(i, map(snd, m)) &*&
           alist_get_by_right(m, i) == k;
  ensures true == map_has_fp(m, k);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) {
            map_has_get_by_right(t, k, i);
          }
        }
    }
  }
  @*/


/*@
  lemma void map_no_dup_keys_alist_get_same<kt>(list<pair<kt, int> > m,
                                                kt k, int i)
  requires true == no_dups(map(fst, m)) &*&
           alist_get_by_right(m, i) == k &*&
           true == mem(i, map(snd, m));
  ensures map_get_fp(m, k) == i;
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key == k) {
            if (ind != i) {
              map_has_get_by_right(t, k, i);
              map_has_to_mem(t, k);
            }
          } else {
            map_no_dup_keys_alist_get_same(t, k, i);
          }
        }
    }
  }
  @*/

/*@
  lemma void gen_entries_get_flow_int(list<pair<int, uint32_t> > entries,
                                      list<pair<int_k,int> > ikeys,
                                      list<pair<ext_k,int> > ekeys,
                                      list<option<flw> > vals,
                                      int_k ik)
  requires true == dmap_has_k1_fp(dmap(ikeys, ekeys, vals), ik) &*&
           true == no_dups(map(fst, ikeys)) &*&
           true == forall(map(fst, entries),
                          (contains)(map(snd, ikeys))) &*&
           true == mem(ik, map(entry_ik,
                               gen_entries(entries, ikeys, ekeys, vals)));
  ensures entry_flow(nth(index_of(ik,
                                  map(entry_ik,
                                      gen_entries(entries, ikeys, ekeys, vals))),
                         gen_entries(entries, ikeys, ekeys, vals))) ==
          dmap_get_val_fp(dmap(ikeys, ekeys, vals),
                          dmap_get_k1_fp(dmap(ikeys, ekeys, vals), ik));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tsmpt):
          if (alist_get_by_right(ikeys, ind) == ik) {
            assert index_of(ik, map(entry_ik, gen_entries(entries, ikeys, ekeys, vals))) == 0;
            map_no_dup_keys_alist_get_same(ikeys, ik, ind);
            assert dmap_get_k1_fp(dmap(ikeys, ekeys, vals), ik) == ind;
          } else {
            gen_entries_get_flow_int(t, ikeys, ekeys, vals, ik);
          }
        }
    }
  }
  @*/

/*@
// Head lemma #
lemma void get_flow_by_int_abstract(dmap<int_k,ext_k,flw> m, dchain ch, int_k ik)
requires true == dmap_has_k1_fp(m, ik) &*&
         dmap_dchain_coherent(m, ch) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  vk1, vk2, recp1, recp2, mp) &*&
        dmap_get_val_fp(m, dmap_get_k1_fp(m, ik)) ==
        flowtable_get_by_int_flow_id(abstract_function(m, ch), ik);
{
  contains_int_k_abstract(m, ch, ik);
  switch(ch) { case dchain(entries, index_range, low, high):
    switch(m) { case dmap(ikeys, ekeys, vals):
      dmap_no_dup_keys(ikeys, ekeys, vals);
      dmap_indexes_used_used_in_ma_mb(ikeys, ekeys, vals);
      coherent_same_indexes(m, ch);
      subset_forall(map(fst, entries), dmap_indexes_used_fp(m),
                    (contains)(map(snd, ikeys)));
      gen_entries_get_flow_int(entries, ikeys, ekeys, vals, ik);
    }
  }
}

// Head lemma #
lemma void get_flow_by_ext_abstract(dmap<int_k,ext_k,flw> m, dchain ch, ext_k ek)
requires true == dmap_has_k2_fp(m, ek) &*&
         dmap_dchain_coherent(m, ch) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   ?vk1, ?vk2, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  vk1, vk2, recp1, recp2, mp) &*&
        dmap_get_val_fp(m, dmap_get_k2_fp(m, ek)) ==
        flowtable_get_by_ext_flow_id(abstract_function(m, ch), ek);
{
  assume(false);//TODO
}
@*/

/*@
  lemma void found_an_opt_dup<kt>(list<option<kt> > vals, int i1, int i2, kt x)
  requires 0 <= i1 &*& i1 < length(vals) &*&
           0 <= i2 &*& i2 < length(vals) &*&
           i1 < i2 &*&
           nth(i1, vals) == some(x) &*& nth(i2, vals) == some(x);
  ensures false == opt_no_dups(vals);
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        if (i1 == 0) {
        }  else {
          found_an_opt_dup(t, i1 - 1, i2 - 1, x);
        }
    }
  }
  @*/

/*@
  lemma void gen_entries_add_flow_light(list<pair<int, uint32_t> > entries,
                                        list<pair<int_k,int> > ikeys,
                                        list<pair<ext_k,int> > ekeys,
                                        list<option<flw> > vals,
                                        int index,
                                        uint32_t time,
                                        flw flow)
  requires nth(index, vals) == some(flow) &*&
           0 <= index &*& index < length(vals) &*&
           alist_get_by_right(ikeys, index) == flw_get_ik(flow) &*&
           alist_get_by_right(ekeys, index) == flw_get_ek(flow);
  ensures gen_entries(append(entries, cons(pair(index, time), nil)),
                      ikeys, ekeys, vals) ==
          append(gen_entries(entries, ikeys, ekeys, vals),
                 cons(entry(flw_get_ik(flow),
                            flw_get_ek(flow),
                            flow,
                            time),
                      nil));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          gen_entries_add_flow_light(t, ikeys, ekeys, vals, index, time, flow);
        }
    }
  }
  @*/

/*@
  lemma void gen_entries_rejuvenate(list<pair<int, uint32_t> > entries,
                                    list<pair<int_k,int> > ikeys,
                                    list<pair<ext_k,int> > ekeys,
                                    list<option<flw> > vals,
                                    int index,
                                    uint32_t time,
                                    flw flow)
  requires nth(index, vals) == some(flow) &*&
           true == mem(index, map(fst, entries)) &*&
           0 <= index &*& index < length(vals) &*&
           alist_get_by_right(ikeys, index) == flw_get_ik(flow) &*&
           alist_get_by_right(ekeys, index) == flw_get_ek(flow) &*&
           true == opt_no_dups(vals) &*&
           true == forall(map(fst, entries), (ge)(0)) &*&
           true == forall(map(fst, entries), (lt)(length(vals))) &*&
           true == forall(map(fst, entries),
                          (dmap_index_used_fp)(dmap(ikeys, ekeys, vals)));
  ensures gen_entries(append(remove_by_index_fp(entries, index),
                             cons(pair(index, time), nil)),
                      ikeys, ekeys, vals) ==
          append(remove_if((entry_matches_flow)(flow),
                           gen_entries(entries, ikeys, ekeys, vals)),
                 cons(entry(flw_get_ik(flow),
                            flw_get_ek(flow),
                            flow,
                            time),
                      nil));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          if (ind == index) {
            gen_entries_add_flow_light(t, ikeys, ekeys, vals,
                                       index, time, flow);
          } else {
            if (nth(ind, vals) == some(flow)) {
              if (ind < index) {
                found_an_opt_dup(vals, ind, index, flow);
              } else {
                found_an_opt_dup(vals, index, ind, flow);
              }
              assert(false);
            }
            assert nth(ind, vals) != some(flow);
            assert nth(ind, vals) != none;
            switch(nth(ind, vals)) {
              case none:
              case some(aaaa):
            }
            assert get_some(nth(ind, vals)) != flow;
            gen_entries_rejuvenate(t, ikeys, ekeys, vals, index, time, flow);
          }
        }
    }
  }
  @*/

/*@
  lemma void get_some_to_some_val<vt>(list<option<vt> > vals, int index, vt v)
  requires 0 <= index &*& index < length(vals) &*&
           nth(index, vals) != none &*&
           get_some(nth(index, vals)) == v;
  ensures nth(index, vals) == some(v);
  {
    switch(vals) {
      case nil:
      case cons(h,t):
        if (index == 0) { switch(h) {
          case none:
          case some(x):
        }} else {
          get_some_to_some_val(t, index - 1, v);
        }
    }
  }
  @*/

/*@
// Head lemma #
lemma void rejuvenate_flow_abstract(dmap<int_k,ext_k,flw> m, dchain ch, flw flow,
                                    int index, uint32_t time)
requires dmap_get_val_fp(m, index) == flow &*&
         true == dmap_index_used_fp(m, index) &*&
         dmap_dchain_coherent(m, ch) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   flw_get_ik, flw_get_ek, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  flw_get_ik, flw_get_ek, recp1, recp2, mp) &*&
        flowtable_add_flow(flowtable_remove_flow(abstract_function(m, ch),
                                                 flow),
                           flow, time) ==
        abstract_function(m, dchain_rejuvenate_fp(ch, index, time));
{
  switch(ch) { case dchain(entries, index_range, low, high):
    switch(m) { case dmap(ikeys, ekeys, vals):
      dmap_no_dup_keys(ikeys, ekeys, vals);
      get_some_to_some_val(vals, index, flow);
      coherent_dmap_used_dchain_allocated(m, ch, index);
      dchain_allocated_mem_map(entries, index_range, low, high, index);
      if (alist_get_by_right(ikeys, index) != flw_get_ik(flow)) {
        int_k alt_ik = alist_get_by_right(ikeys, index);
        dmap_indexes_used_used_in_ma_mb(ikeys, ekeys, vals);
        dmap_indexes_contain_index_used(m, index);
        forall_mem(index, dmap_indexes_used_fp(m), (contains)(map(snd, ikeys)));
        map_has_get_by_right(ikeys, alt_ik, index);
        map_no_dup_keys_alist_get_same(ikeys, alt_ik, index);
        assert dmap_get_k1_fp(m, alt_ik) == index;
        dmap_get_by_k1_invertible(m, alt_ik);
        assert flw_get_ik(dmap_get_val_fp(m, index)) == alt_ik;
        assert alt_ik != flw_get_ik(flow);
        assert dmap_get_val_fp(m, index) != flow;
      }
      if (alist_get_by_right(ekeys, index) != flw_get_ek(flow)) {
        ext_k alt_ek = alist_get_by_right(ekeys, index);
        dmap_indexes_used_used_in_ma_mb(ikeys, ekeys, vals);
        dmap_indexes_contain_index_used(m, index);
        forall_mem(index, dmap_indexes_used_fp(m), (contains)(map(snd, ekeys)));
        map_has_get_by_right(ekeys, alt_ek, index);
        map_no_dup_keys_alist_get_same(ekeys, alt_ek, index);
        assert dmap_get_k2_fp(m, alt_ek) == index;
        dmap_get_by_k2_invertible(m, alt_ek);
        assert flw_get_ek(dmap_get_val_fp(m, index)) == alt_ek;
        assert alt_ek != flw_get_ek(flow);
        assert dmap_get_val_fp(m, index) != flow;
      }
      assert alist_get_by_right(ikeys, index) == flw_get_ik(flow);
      dmap_no_dup_vals(ikeys, ekeys, vals);
      nonempty_indexes_bounds(vals, 0);
      coherent_same_indexes(m, ch);
      subset_forall(map(fst, entries), dmap_indexes_used_fp(m), (ge)(0));
      subset_forall(map(fst, entries), dmap_indexes_used_fp(m),
                    (lt)(length(vals)));

      dmap_all_used_indexes_used(ikeys, ekeys, vals);
      assert true == forall(nonempty_indexes_fp(vals, 0), (dmap_index_used_fp)(m));
      subset_forall(map(fst, entries), dmap_indexes_used_fp(m),
                    (dmap_index_used_fp)(m));
      gen_entries_rejuvenate(entries, ikeys, ekeys, vals, index, time, flow);
    }
  }
}
@*/
/*@
  fixpoint list<entry> expire_one_entry(list<entry> entries, uint32_t time) {
    switch(entries) {
      case nil: return nil;
      case cons(h,t):
        return entry_tstamp(h) < time ?
               t :
               cons(h, expire_one_entry(t, time));
    }

  }
  fixpoint flowtable flowtable_expire_one(flowtable ft, uint32_t time) {
    switch(ft) { case flowtable(size, entries):
      return flowtable(size, expire_one_entry(entries, time));
    }
  }

  fixpoint bool has_expired_entry(list<entry> entries, uint32_t time) {
    switch(entries) {
      case nil: return false;
      case cons(h,t):
        return entry_tstamp(h) < time ? true : has_expired_entry(t, time);
    }
  }

  fixpoint bool flowtable_has_expired_flow(flowtable ft, uint32_t time) {
    switch(ft) { case flowtable(size, entries):
      return has_expired_entry(entries, time);
    }
  }
  @*/

/*@
  lemma void expire_0_entries(list<entry> entries, uint32_t time)
  requires true;
  ensures expire_n_entries(entries, time, 0) == entries;
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case entry(ik, ek, flw, tstmp):
          if (tstmp < time) expire_0_entries(t, time);
        }
    }
  }
  @*/

/*@
  lemma void expire_one_more_entry(list<entry> entries, uint32_t time, int count)
  requires true == has_expired_entry(expire_n_entries(entries, time, count),
                                     time) &*&
           0 <= count;
  ensures expire_n_entries(entries, time, count + 1) ==
          expire_one_entry(expire_n_entries(entries, time, count), time);
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case entry(ik, ek, fl, tstmp):
          if (count == 0) {
            expire_0_entries(entries, time);
            expire_0_entries(t, time);
            if (time <= tstmp) {
              assert true == has_expired_entry(t, time);
              expire_one_more_entry(t, time, count);
            }
          } else {
            if (time <= tstmp) {
              expire_one_more_entry(t, time, count);
            } else {
              expire_one_more_entry(t, time, count - 1);
            }
          }
        }
    }
  }
  @*/

/*@
  lemma void flowtable_expire_one_more_plus1(flowtable ft, uint32_t time,
                                             int count)
  requires true == flowtable_has_expired_flow
                     (flowtable_expire_n_flows(ft, time, count), time) &*&
           0 <= count;
  ensures flowtable_expire_n_flows(ft, time, count + 1) ==
          flowtable_expire_one(flowtable_expire_n_flows(ft, time, count), time);
  {
    switch(ft) { case flowtable(size, entries):
      expire_one_more_entry(entries, time, count);
    }
  }
  @*/

/*@
  lemma void remove_unrelevant_keeps_alist_get_by_right<kt>(list<pair<kt, int> > m,
                                                            kt k, int ind)
  requires map_get_fp(m, k) != ind;
  ensures alist_get_by_right(map_erase_fp(m, k), ind) == alist_get_by_right(m, ind);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,i):
          if (i == ind) {
          } else if (key == k) {
          } else {
            remove_unrelevant_keeps_alist_get_by_right(t, k, ind);
          }

        }
    }
  }
  @*/

/*@
  lemma void gen_entries_remove_extra(list<pair<int, uint32_t> > entries,
                                      list<pair<int_k,int> > ikeys,
                                      list<pair<ext_k,int> > ekeys,
                                      list<option<flw> > vals,
                                      int index,
                                      int_k ik,
                                      ext_k ek)
  requires false == mem(index, map(fst, entries)) &*&
           map_get_fp(ikeys, ik) == index &*&
           map_get_fp(ekeys, ek) == index &*&
           0 <= index &*& index < length(vals) &*&
           true == forall(map(fst, entries), (ge)(0)) &*&
           true == forall(map(fst, entries), (lt)(length(vals)));
  ensures gen_entries(entries, ikeys, ekeys, vals) ==
          gen_entries(entries, map_erase_fp(ikeys, ik),
                      map_erase_fp(ekeys, ek),
                      update(index, none, vals));
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind,tstmp):
          assert ind != index;
          remove_unrelevant_keeps_alist_get_by_right(ikeys, ik, ind);
          remove_unrelevant_keeps_alist_get_by_right(ekeys, ek, ind);
          assert alist_get_by_right(ikeys, ind) ==
                 alist_get_by_right(map_erase_fp(ikeys, ik), ind);
          gen_entries_remove_extra(t, ikeys, ekeys, vals, index, ik, ek);
        }
    }
  }
  @*/


/*@
  lemma void gen_entries_expire_just_one(pair<int, uint32_t> hdentry,
                                         list<pair<int, uint32_t> > entries,
                                         list<pair<int_k,int> > ikeys,
                                         list<pair<ext_k,int> > ekeys,
                                         list<option<flw> > vals,
                                         int index,
                                         uint32_t time,
                                         flw flow)
  requires fst(hdentry) == index &*&
           nth(index, vals) == some(flow) &*&
           map_get_fp(ikeys, flw_get_ik(flow)) == index &*&
           map_get_fp(ekeys, flw_get_ek(flow)) == index &*&
           0 <= index &*& index < length(vals) &*&
           snd(hdentry) < time &*&
           true == forall(map(fst, entries), (ge)(0)) &*&
           true == forall(map(fst, entries), (lt)(length(vals))) &*&
           false == mem(index, map(fst, entries));
  ensures gen_entries(entries,
                      map_erase_fp(ikeys, flw_get_ik(flow)),
                      map_erase_fp(ekeys, flw_get_ek(flow)),
                      update(index, none, vals)) ==
          expire_one_entry(gen_entries(cons(hdentry, entries), ikeys, ekeys, vals),
                           time);
  {
    assert entry_tstamp(entry(alist_get_by_right(ikeys, index),
                             alist_get_by_right(ekeys, index),
                             get_some(nth(index, vals)),
                             snd(hdentry))) < time;
    switch(hdentry) {
      case pair(iii,ttt):
    }
    assert gen_entries(entries, ikeys, ekeys, vals) ==
           expire_one_entry(gen_entries(cons(hdentry, entries), ikeys, ekeys, vals), time);
    gen_entries_remove_extra(entries, ikeys, ekeys, vals,
                             index, flw_get_ik(flow), flw_get_ek(flow));
  }
  @*/

/*@
  lemma void expire_just_one_abstract(dmap<int_k,ext_k,flw> m,
                                      dchain ch, uint32_t time)
  requires false == dchain_is_empty_fp(ch) &*&
           dchain_get_oldest_time_fp(ch) < time &*&
           true == dmap_self_consistent_integral_fp(m, flw_get_ik,
                                                    flw_get_ek) &*&
           true == forall(dchain_indexes_fp(ch), (ge)(0)) &*&
           true == forall(dchain_indexes_fp(ch), (lt)(dmap_cap_fp(m))) &*&
           true == distinct(dchain_indexes_fp(ch)) &*&
           true == forall(dchain_indexes_fp(ch),
                          (dmap_index_used_fp)(m));
  ensures abstract_function(dmap_erase_fp(m, dchain_get_oldest_index_fp(ch),
                                          flw_get_ik, flw_get_ek),
                            dchain_remove_index_fp
                              (ch, dchain_get_oldest_index_fp(ch))) ==
          flowtable_expire_one(abstract_function(m, ch), time);
  {
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        switch(entries) {
          case nil: assert false;
          case cons(ent,t): switch(ent) { case pair(ind,tstmp):
            assert nth(ind, vals) != none;
            switch(nth(ind, vals)) {
              case none:
              case some(xxxx):
            }
            dmap_consistent_right_indexes(m, flw_get_ik, flw_get_ek, ind);
            gen_entries_expire_just_one(ent, t, ikeys, ekeys, vals,
                                        ind, time,
                                        get_some(nth(ind, vals)));
          }
        }
      }
    }
  }
  @*/

/*@
  lemma void dchain_expire_some_still_olds_left(dchain ch,
                                                uint32_t time, int count)
  requires count < length(dchain_get_expired_indexes_fp(ch, time));
  ensures false == dchain_is_empty_fp(expire_n_indexes(ch, time, count)) &*&
          dchain_get_oldest_time_fp(expire_n_indexes(ch, time, count)) < time;
  {
    assume(false);//TODO
  }
  @*/

/*@
  lemma void dchain_has_expired_ft_also(dmap<int_k,ext_k,flw> m,
                                        dchain ch, uint32_t time)
  requires false == dchain_is_empty_fp(ch) &*&
           dchain_get_oldest_time_fp(ch) < time;
  ensures true == flowtable_has_expired_flow(abstract_function(m, ch), time);
  {
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        switch(entries) {
          case nil: assert false;
          case cons(h,t):
            switch(h) { case pair(ind,tstmp):
            }
        }
      }
    }
  }
  @*/


/*@
  lemma void dchain_indexes_expire_n_subset(dchain ch, uint32_t time, int n)
  requires true;
  ensures true == subset(dchain_indexes_fp(expire_n_indexes(ch, time, n)),
                         dchain_indexes_fp(ch));
  {
    assume(false);//TODO 
  }
  @*/


/*@
  lemma void remove_by_index_still_nonmem(list<pair<int, uint32_t> > l,
                                          int x, int y)
  requires false == mem(x, map(fst, l));
  ensures false == mem(x, map(fst, remove_by_index_fp(l, y)));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind, tstmp):
          if (ind != y) remove_by_index_still_nonmem(t, x, y);
        }
    }
  }
  @*/

/*@
  lemma void remove_by_index_still_distinct(list<pair<int, uint32_t> > l, int i)
  requires true == distinct(map(fst, l));
  ensures true == distinct(map(fst, remove_by_index_fp(l, i)));
  {
    switch(l) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind, tstmp):
          if (ind == i) {
          } else {
            remove_by_index_still_distinct(t, i);
            remove_by_index_still_nonmem(t, ind, i);
          }
        }
    }
  }
  @*/


/*@
  lemma void dchain_expire_n_still_distinct(dchain ch, uint32_t time, int n)
  requires true == distinct(dchain_indexes_fp(ch)) &*&
           0 <= n &*& n <= length(dchain_get_expired_indexes_fp(ch, time));
  ensures true == distinct(dchain_indexes_fp(expire_n_indexes(ch, time, n)));
  {
    switch(ch) { case dchain(entries, index_range, low, high):
      int i = 0;
      list<int> indices = get_expired_indexes_fp(time, entries);
      for (; i < n; ++i)
        invariant true == distinct(map(fst,
                                       fold_left(entries,
                                                 remove_by_index_fp,
                                                 take(i, indices)))) &*&
                  0 <= i &*& i <= n;
        decreases n - i;
      {
        fold_left_append(entries, remove_by_index_fp, take(i, indices),
                         cons(nth(i, indices), nil));
        append_take_nth_to_take(indices, i);
        remove_by_index_still_distinct(fold_left(entries,
                                                 remove_by_index_fp,
                                                 take(i, indices)),
                                       nth(i, indices));
      }
    }
  }
  @*/


/*@
  lemma void oldest_index_is_mem_of_indices(dchain ch)
  requires false == dchain_is_empty_fp(ch);
  ensures true == mem(dchain_get_oldest_index_fp(ch),
                      dchain_indexes_fp(ch));
  {
    switch(ch) { case dchain(entries, irange, low, high):
      switch(entries) {
        case nil:
        case cons(h,t):
      }
    }
  }
  @*/

/*@
  lemma void indices_used_expire_some<t1,t2,vt>(dchain ch,
                                                dmap<t1,t2,vt> m,
                                                uint32_t time,
                                                fixpoint (vt,t1) vk1,
                                                fixpoint (vt,t2) vk2,
                                                int n)
  requires true == forall(dchain_indexes_fp(ch), (dmap_index_used_fp)(m));
  ensures true == forall(dchain_indexes_fp(expire_n_indexes(ch, time, n)),
                         (dmap_index_used_fp)
                            (dmap_erase_all_fp
                               (m, take(n, dchain_get_expired_indexes_fp
                                             (ch, time)),
                                vk1, vk2)));
  {
    assume(false);//TODO 
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
    assume(false);//TODO 
  }
  @*/

/*@
  lemma void expire_one_more_flow(dmap<int_k,ext_k,flw> m,
                                  dchain ch, uint32_t time,
                                  int count)
  requires dmap_dchain_coherent(m, ch) &*&
           dchain_is_sortedp(ch) &*&
           0 <= count &*&
           count < length(dchain_get_expired_indexes_fp(ch, time)) &*&
           true == forall(dchain_indexes_fp(ch), (dmap_index_used_fp)(m)) &*&
           true == forall(dchain_indexes_fp(ch), (ge)(0)) &*&
           true == forall(dchain_indexes_fp(ch), (lt)(dmap_cap_fp(m))) &*&
           true == distinct(dchain_indexes_fp(ch)) &*&
           true == dmap_self_consistent_integral_fp
                     (dmap_erase_all_fp
                        (m, take(count,
                                 dchain_get_expired_indexes_fp(ch, time)),
                         flw_get_ik, flw_get_ek),
                      flw_get_ik,
                      flw_get_ek) &*&
           flowtable_expire_n_flows(abstract_function(m, ch), time, count) ==
           abstract_function(dmap_erase_all_fp
                               (m, take(count,
                                        dchain_get_expired_indexes_fp(ch, time)),
                                flw_get_ik, flw_get_ek),
                             expire_n_indexes(ch, time, count));
  ensures dmap_dchain_coherent(m, ch) &*&
          dchain_is_sortedp(ch) &*&
          true == dmap_self_consistent_integral_fp
                    (dmap_erase_all_fp
                      (m, take(count + 1,
                                dchain_get_expired_indexes_fp(ch, time)),
                        flw_get_ik, flw_get_ek),
                    flw_get_ik,
                    flw_get_ek) &*&
          flowtable_expire_n_flows(abstract_function(m, ch), time, count + 1) ==
          abstract_function(dmap_erase_all_fp
                             (m, take(count + 1,
                                      dchain_get_expired_indexes_fp(ch, time)),
                              flw_get_ik, flw_get_ek),
                            expire_n_indexes(ch, time, count + 1));
  {
    dchain_expire_some_still_olds_left(ch, time, count);
    dchain_indexes_expire_n_subset(ch, time, count);
    subset_forall(dchain_indexes_fp(expire_n_indexes(ch, time, count)),
                  dchain_indexes_fp(ch),
                  (ge)(0));
    subset_forall(dchain_indexes_fp(expire_n_indexes(ch, time, count)),
                  dchain_indexes_fp(ch),
                  (lt)(dmap_cap_fp(m)));
    dmap_erase_all_preserves_cap(m, take(count,
                                         dchain_get_expired_indexes_fp(ch, time)),
                                 flw_get_ik, flw_get_ek);
    dchain_expire_n_still_distinct(ch, time, count);
    indices_used_expire_some(ch, m, time, flw_get_ik, flw_get_ek, count);
    expire_just_one_abstract(dmap_erase_all_fp
                               (m, take(count,
                                        dchain_get_expired_indexes_fp(ch, time)),
                                flw_get_ik, flw_get_ek),
                             expire_n_indexes(ch, time, count),
                             time);
    dchain_has_expired_ft_also(dmap_erase_all_fp
                                 (m, take(count,
                                          dchain_get_expired_indexes_fp(ch, time)),
                                  flw_get_ik, flw_get_ek),
                               expire_n_indexes(ch, time, count),
                               time);
    flowtable ftbef = flowtable_expire_n_flows(abstract_function(m, ch),
                                               time, count);
    flowtable_expire_one_more_plus1(abstract_function(m, ch), time, count);
    expire_n_plus_one(ch, time, count);
    dmap_erase_another_one(m, take(count,
                                   dchain_get_expired_indexes_fp(ch, time)),
                           dchain_get_oldest_index_fp
                             (expire_n_indexes(ch, time, count)),
                           flw_get_ik, flw_get_ek);
    oldest_index_is_mem_of_indices(expire_n_indexes(ch, time, count));
    forall_mem(dchain_get_oldest_index_fp(expire_n_indexes(ch, time, count)),
               dchain_indexes_fp(expire_n_indexes(ch, time, count)),
               (dmap_index_used_fp)
                 (dmap_erase_all_fp(m, take(count,
                                            dchain_get_expired_indexes_fp(ch, time)),
                                    flw_get_ik, flw_get_ek)));
    dmap_erase_self_consistent
      (dmap_erase_all_fp(m, take(count, dchain_get_expired_indexes_fp(ch, time)),
                         flw_get_ik, flw_get_ek),
       dchain_get_oldest_index_fp(expire_n_indexes(ch, time, count)),
       flw_get_ik, flw_get_ek);
  }
  @*/

/*@
  lemma void expire_0_indexes(dchain ch, uint32_t time)
  requires true;
  ensures ch == expire_n_indexes(ch, time, 0);
  {
    switch(ch) { case dchain(alist, size, l, h):
      take_0(get_expired_indexes_fp(time, alist));
    }
  }
  @*/

/*@
  lemma void flowtable_expire_0_flows(flowtable ft, uint32_t time)
  requires true;
  ensures flowtable_expire_n_flows(ft, time, 0) == ft;
  {
    switch(ft) { case flowtable(size, entries):
      expire_0_entries(entries, time);
    }
  }
  @*/

/*@
  lemma void gen_entries_expire_them_all(list<pair<int, uint32_t> > entries,
                                         list<pair<int_k,int> > ikeys,
                                         list<pair<ext_k,int> > ekeys,
                                         list<option<flw> > vals,
                                         uint32_t time)
  requires true;
  ensures expire_n_entries(gen_entries(entries, ikeys, ekeys, vals), time,
                           length(get_expired_indexes_fp(time, entries))) ==
          expire_entries(gen_entries(entries, ikeys, ekeys, vals), time);
  {
    switch(entries) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(ind, tstmp):
          if (tstmp < time) {
            gen_entries_expire_them_all(t, ikeys, ekeys, vals, time);
          } else {
            gen_entries_expire_them_all(t, ikeys, ekeys, vals, time);
            int ll = length(get_expired_indexes_fp(time, t));
            if (ll == 0) {
              expire_0_entries(gen_entries(entries, ikeys, ekeys, vals), time);
              expire_0_entries(gen_entries(t, ikeys, ekeys, vals), time);
            }
          }
        }
    }
  }
  @*/

/*@
  lemma void flowtable_expire_them_all(dmap<int_k,ext_k,flw> m,
                                       dchain ch, uint32_t time)
  requires true;
  ensures flowtable_expire_n_flows
            (abstract_function(m, ch), time,
             length(dchain_get_expired_indexes_fp(ch, time))) ==
          flowtable_expire_flows(abstract_function(m, ch), time);
  {
    switch(ch) { case dchain(entries, index_range, low, high):
      switch(m) { case dmap(ikeys, ekeys, vals):
        gen_entries_expire_them_all(entries, ikeys, ekeys, vals, time);
      }
    }
  }
  @*/

/*@
  lemma void dchain_expire_them_all(dchain ch, uint32_t time)
  requires true;
  ensures expire_n_indexes(ch, time,
                           length(dchain_get_expired_indexes_fp(ch, time))) ==
          dchain_expire_old_indexes_fp(ch, time);
  {
    assume(false);//TODO
  }
  @*/

/*@
// Head lemma #
lemma void expire_flows_abstract(dmap<int_k,ext_k,flw> m,
                                 dchain ch, uint32_t time)
requires dmap_dchain_coherent(m, ch) &*&
         double_chainp(ch, ?ppp) &*&
         dmappingp(m, ?kp1, ?kp2, ?hsh1, ?hsh2,
                   ?fvp, ?bvp, ?rof, ?vsz,
                   flw_get_ik, flw_get_ek, ?recp1, ?recp2, ?mp);
ensures dmap_dchain_coherent(m, ch) &*&
        double_chainp(ch, ppp) &*&
        dmappingp(m, kp1, kp2, hsh1, hsh2,
                  fvp, bvp, rof, vsz,
                  flw_get_ik, flw_get_ek, recp1, recp2, mp) &*&
        flowtable_expire_flows(abstract_function(m, ch), time) ==
        abstract_function(dmap_erase_all_fp
                            (m, dchain_get_expired_indexes_fp(ch, time),
                             flw_get_ik, flw_get_ek),
                          dchain_expire_old_indexes_fp(ch, time));
{
  list<int> exp_indices = dchain_get_expired_indexes_fp(ch, time);
  expire_0_indexes(ch, time);
  flowtable_expire_0_flows(abstract_function(m, ch), time);
  double_chainp_to_sorted(ch);
  coherent_same_indexes(m, ch);
  switch(m) { case dmap(ikeys, ekeys, vals):
    nonempty_indexes_bounds(vals, 0);
    dmap_all_used_indexes_used(ikeys, ekeys, vals);
  }
  subset_forall(dchain_indexes_fp(ch), dmap_indexes_used_fp(m), (ge)(0));
  subset_forall(dchain_indexes_fp(ch), dmap_indexes_used_fp(m),
                (lt)(dmap_cap_fp(m)));
  subset_forall(dchain_indexes_fp(ch), dmap_indexes_used_fp(m),
                (dmap_index_used_fp)(m));
  dchain_distinct_indexes(ch);
  dmap_pred_self_consistent(m);
  int count = 0;
  for (; count < length(exp_indices); ++count)
    invariant dmap_dchain_coherent(m, ch) &*&
              dchain_is_sortedp(ch) &*&
              0 <= count &*& count <= length(exp_indices) &*&
              true == forall(dchain_indexes_fp(ch), (dmap_index_used_fp)(m)) &*&
              true == forall(dchain_indexes_fp(ch), (ge)(0)) &*&
              true == forall(dchain_indexes_fp(ch), (lt)(dmap_cap_fp(m))) &*&
              true == distinct(dchain_indexes_fp(ch)) &*&
              true == dmap_self_consistent_integral_fp
                        (dmap_erase_all_fp
                           (m, take(count,
                                    dchain_get_expired_indexes_fp(ch, time)),
                            flw_get_ik, flw_get_ek),
                         flw_get_ik, flw_get_ek) &*&
              flowtable_expire_n_flows(abstract_function(m, ch), time, count) ==
              abstract_function(dmap_erase_all_fp
                                  (m, take(count, exp_indices),
                                   flw_get_ik, flw_get_ek),
                                expire_n_indexes(ch, time, count));
    decreases length(exp_indices) - count;
  {
    expire_one_more_flow(m, ch, time, count);
  }
  dchain_expire_them_all(ch, time);
  flowtable_expire_them_all(m, ch, time);
  destroy_dchain_is_sortedp(ch);
}
@*/
