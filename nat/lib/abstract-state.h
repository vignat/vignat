#include "containers/double-map.h"
#include "containers/double-chain.h"
#include "flow.h"

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
    return flowtable(size, cons(entry(flw_get_ik(flow),
                                      flw_get_ek(flow),
                                      flow,
                                      time),
                                entries));
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
lemma void contains_ext_k_abstract(dmap<int_k,ext_k,flw> m, dchain ch,
                                   ext_k ek)
requires true;
ensures flowtable_contains_ext_flow_id(abstract_function(m, ch), ek) ==
        dmap_has_k2_fp(m, ek);
{
  assume(false);//TODO
}

lemma void contains_int_k_abstract(dmap<int_k,ext_k,flw> m, dchain ch,
                                   int_k ik)
requires true;
ensures flowtable_contains_int_flow_id(abstract_function(m, ch), ik) ==
        dmap_has_k1_fp(m, ik);
{
  assume(false);//TODO
}

lemma void out_of_space_abstract(dmap<int_k,ext_k,flw> m, dchain ch)
requires true;
ensures flowtable_out_of_space(abstract_function(m, ch)) ==
        dchain_out_of_space_fp(ch);
{
  assume(false);//TODO
}

lemma void add_flow_abstract(dmap<int_k,ext_k,flw> m, dchain ch, flw flow,
                             int index, uint32_t t)
requires false == dchain_out_of_space_fp(ch) &*&
         false == dchain_allocated_fp(ch, index);
ensures flowtable_add_flow(abstract_function(m, ch), flow, t) ==
        abstract_function(dmap_put_fp(m, index, flow, flw_get_ik, flw_get_ek),
                          dchain_allocate_fp(ch, index, t));
{
  assume(false);//TODO
}

lemma void get_flow_by_int_abstract(dmap<int_k,ext_k,flw> m, dchain ch, int_k ik)
requires true == dmap_has_k1_fp(m, ik);
ensures dmap_get_val_fp(m, dmap_get_k1_fp(m, ik)) ==
        flowtable_get_by_int_flow_id(abstract_function(m, ch), ik);
{
  assume(false);//TODO
}

lemma void get_flow_by_ext_abstract(dmap<int_k,ext_k,flw> m, dchain ch, ext_k ek)
requires true == dmap_has_k2_fp(m, ek);
ensures dmap_get_val_fp(m, dmap_get_k2_fp(m, ek)) ==
        flowtable_get_by_ext_flow_id(abstract_function(m, ch), ek);
{
  assume(false);//TODO
}

lemma void rejuvenate_flow_abstract(dmap<int_k,ext_k,flw> m, dchain ch, flw flow,
                                    int index, uint32_t time)
requires dmap_get_val_fp(m, index) == flow;
ensures flowtable_add_flow(flowtable_remove_flow(abstract_function(m, ch),
                                                 flow),
                           flow, time) ==
        abstract_function(m, dchain_rejuvenate_fp(ch, index, time));
{
  assume(false);//TODO
}

lemma void expire_flows_abstract(dmap<int_k,ext_k,flw> m,
                                 dchain ch, uint32_t time)
requires true;
ensures flowtable_expire_flows(abstract_function(m, ch), time) ==
        abstract_function(dmap_erase_all_fp
                            (m, dchain_get_expired_indexes_fp(ch, time),
                             flw_get_ik, flw_get_ek),
                          dchain_expire_old_indexes_fp(ch, time));
{
  assume(false);//TODO
}
@*/
