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

fixpoint list<entry> gen_entries(list<pair<int, uint32_t> > indexes,
                                 list<pair<int_k, int> > ikeys,
                                 list<pair<ext_k, int> > ekeys,
                                 list<option<flw> > flows) {
  switch(indexes) {
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
    case cons(h,t): return time < entry_tstamp(h)           ?
                           cons(h, expire_entries(t, time)) :
                           expire_entries(t, time);
  }
}

fixpoint flowtable flowtable_expire_flows(flowtable table, uint32_t time) {
  switch(table) { case flowtable(size, entries):
    return flowtable(size, expire_entries(entries, time));
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
  lemma void map_has_mem<kt,vt>(list<pair<kt,vt> > m, kt k)
  requires true;
  ensures mem(k, map(fst, m)) == map_has_fp(m, k);
  {
    switch(m) {
      case nil:
      case cons(h,t):
        switch(h) { case pair(key,ind):
          if (key != k) map_has_mem(t, k);
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
        map_has_mem(ekeys, ek);
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
  assume(false);//TODO
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
//Head lemma #
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
  lemma void nonempty_indexes_bounds<vt>(list<option<vt> > lst, int start)
  requires true;
  ensures true == forall(nonempty_indexes_fp(lst, start), (ge)(start)) &*&
          true == forall(nonempty_indexes_fp(lst, start), (lt)(start + length(lst)));
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        switch(h) {
          case none:
          case some(x):
        }
        nonempty_indexes_bounds(t, start + 1);
        ge_le_ge(nonempty_indexes_fp(t, start+1), start + 1, start);
    }
  }
  @*/


/*@
//Head lemma #
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
              map_has_mem(t, k);
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
//Head lemma #
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

lemma void rejuvenate_flow_abstract(dmap<int_k,ext_k,flw> m, dchain ch, flw flow,
                                    int index, uint32_t time)
requires dmap_get_val_fp(m, index) == flow &*&
         dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, ch) &*&
        flowtable_add_flow(flowtable_remove_flow(abstract_function(m, ch),
                                                 flow),
                           flow, time) ==
        abstract_function(m, dchain_rejuvenate_fp(ch, index, time));
{
  assume(false);//TODO
}

lemma void expire_flows_abstract(dmap<int_k,ext_k,flw> m,
                                 dchain ch, uint32_t time)
requires dmap_dchain_coherent(m, ch);
ensures dmap_dchain_coherent(m, ch) &*&
        flowtable_expire_flows(abstract_function(m, ch), time) ==
        abstract_function(dmap_erase_all_fp
                            (m, dchain_get_expired_indexes_fp(ch, time),
                             flw_get_ik, flw_get_ek),
                          dchain_expire_old_indexes_fp(ch, time));
{
  assume(false);//TODO
}
@*/
