#include "containers/double-map.h"
#include "containers/double-chain.h"
#include "coherence.h"
#include "bridge/bridge_data.h"

/*@
  inductive dyn_entry = dyn_entry(ether_addri, uint16_t, uint32_t);
  inductive stat_entry = stat_entry(stat_keyi, int);

  inductive ml_table = ml_table(list<dyn_entry>, list<stat_entry>, int);

  fixpoint list<dyn_entry> get_dyn_table(ml_table table) {
    switch(table) {
      case ml_table(dyn_table, stat_table, capacity):
        return dyn_table;
    }
  }

  fixpoint list<stat_entry> get_stat_table(ml_table table) {
    switch(table) {
      case ml_table(dyn_table, stat_table, capacity):
        return stat_table;
    }
  }

  fixpoint bool stat_table_has_key(list<stat_entry> table, stat_keyi key) {
    switch(table) {
      case nil: return false;
      case cons(h,t):
        return switch(h) { case stat_entry(k,v):
          return (k == key) ? true : stat_table_has_key(t, key);
        };
    }
  }

  fixpoint int stat_table_get(list<stat_entry> table, stat_keyi key) {
    switch(table) {
      case nil: return 0;
      case cons(h,t):
        return switch(h) { case stat_entry(k,v):
          return (k == key) ? v : stat_table_get(t, key);
        };
    }
  }

  fixpoint bool dyn_table_has_key(list<dyn_entry> table, ether_addri key) {
    switch(table) {
      case nil: return false;
      case cons(h,t):
        return switch(h) { case dyn_entry(k,v,timestamp):
           return (k == key) ? true : dyn_table_has_key(t, key);
        };
    }
  }

  fixpoint bool dyn_table_out_of_space(ml_table t) {
    switch(t) { case ml_table(dyn_table, stat_table, capacity):
      return capacity <= length(dyn_table);
    }
  }

  fixpoint uint16_t dyn_table_get(list<dyn_entry> table, ether_addri key) {
    switch(table) {
      case nil: return 0;
      case cons(h,t):
        return switch(h) { case dyn_entry(k,v,timestamp):
           return (k == key) ? v : dyn_table_get(t, key);
        };
    }
  }

  fixpoint list<dyn_entry> gen_dyn_entries(list<pair<ether_addri, int> > table,
                                           list<pair<uint16_t, bool> > values,
                                           dchain indices) {
    switch(table) {
      case nil: return nil;
      case cons(h, t): return switch(h) { case pair(addr, index):
        return cons(dyn_entry(addr,
                              fst(nth(index, values)),
                              dchain_get_time_fp(indices, index)),
                    gen_dyn_entries(t, values, indices));
      };
    }
  }

  fixpoint list<stat_entry> gen_stat_entries(list<pair<stat_keyi, uint16_t> > table) {
    switch(table) {
      case nil: return nil;
      case cons(h, t): return switch(h) { case pair(key, port):
        return cons(stat_entry(key, port),
                    gen_stat_entries(t));
      };
    }
  }

  fixpoint ml_table bridge_abstract_function(mapi<ether_addri> dyn_map,
                                             list<pair<uint16_t, bool> > vals,
                                             dchain indices,
                                             mapi<stat_keyi> stat_map) {
    switch(dyn_map) { case mapc(dyn_capacity, dm, daddrs):
      return switch(stat_map) { case mapc(stat_capacity, sm, saddrs):
        return ml_table(gen_dyn_entries(dm, vals, indices), gen_stat_entries(sm), dyn_capacity);
      };
    }
  }

  fixpoint list<dyn_entry> add_dyn_entry(list<dyn_entry> table,
                                         ether_addri addr,
                                         uint16_t port,
                                         time_t time) {

    return cons(dyn_entry(addr, port, time), table);
  }

  fixpoint list<dyn_entry> rejuvenate_dyn_entry(list<dyn_entry> table,
                                                ether_addri addr_to_rej,
                                                uint32_t new_time) {
    switch(table) {
      case nil: return nil;
      case cons(h,t):
        return switch(h) { case dyn_entry(addr, port, time):
          return (addr == addr_to_rej) ?
                   cons(dyn_entry(addr, port, new_time), t) :
                   cons(h, rejuvenate_dyn_entry(t, addr_to_rej, new_time));
        };
    }
  }

  fixpoint list<dyn_entry> expire_addresses(list<dyn_entry> table, uint32_t now) {
    switch(table) {
      case nil: return nil;
      case cons(h,t):
        return switch(h) { case dyn_entry(addr, port, time):
          return (time < now) ? expire_addresses(t, now) : cons(h, expire_addresses(t, now));
        };
    }
  }

  lemma void bridge_expire_abstract(list<pair<ether_addri, uint32_t> > dyn_map,
                                    list<pair<uint16_t, bool> > vals,
                                    list<pair<ether_addri, bool> > keys,
                                    dchain indices,
                                    time_t time);
  requires true;
  ensures set_eq(gen_dyn_entries(map_erase_all_fp
                                  (dyn_map,
                                   vector_get_values_fp
                                     (keys, dchain_get_expired_indexes_fp
                                              (indices, time))),
                                 vals,
                                 dchain_expire_old_indexes_fp(indices, time)),
                 expire_addresses(gen_dyn_entries(dyn_map, vals, indices),
                                  time)) == true;

  lemma void bridge_add_entry(list<pair<ether_addri, uint32_t> > dyn_map,
                              list<pair<uint16_t, bool> > vals,
                              dchain indices,
                              ether_addri addr,
                              uint32_t index,
                              uint16_t port,
                              time_t time);
  requires true;
  ensures set_eq(gen_dyn_entries(map_put_fp(dyn_map, addr, index),
                                 update(index, pair(port, true), vals),
                                 dchain_allocate_fp(indices, index, time)),
                 add_dyn_entry(gen_dyn_entries(dyn_map, vals, indices),
                               addr, port, time)) == true;

  lemma void bridge_rejuv_entry(list<pair<ether_addri, uint32_t> > dyn_map,
                                list<pair<uint16_t, bool> > vals,
                                dchain indices,
                                ether_addri addr,
                                time_t time);
  requires true;
  ensures set_eq(gen_dyn_entries(dyn_map,
                                 vals,
                                 dchain_rejuvenate_fp(indices, map_get_fp(dyn_map, addr), time)),
                 rejuvenate_dyn_entry(gen_dyn_entries(dyn_map, vals, indices),
                                      addr, time)) == true;

  lemma void bridge_rejuv_entry_set_eq(list<dyn_entry> dyn_table1,
                                       list<dyn_entry> dyn_table2,
                                       ether_addri addr,
                                       time_t time);
  requires true == set_eq(dyn_table1, dyn_table2);
  ensures true == set_eq(rejuvenate_dyn_entry(dyn_table1, addr, time),
                         rejuvenate_dyn_entry(dyn_table2, addr, time));

  lemma void bridge_add_entry_set_eq(list<dyn_entry> dyn_table1,
                                     list<dyn_entry> dyn_table2,
                                     ether_addri addr,
                                     uint16_t port,
                                     time_t time);
  requires true == set_eq(dyn_table1, dyn_table2);
  ensures true == set_eq(add_dyn_entry(dyn_table1, addr, port, time),
                         add_dyn_entry(dyn_table2, addr, port, time));

  lemma void stat_map_has(list<pair<stat_keyi, uint16_t> > map, stat_keyi key);
  requires true;
  ensures map_has_fp(map, key)== stat_table_has_key(gen_stat_entries(map), key);

  lemma void dyn_map_has(list<pair<ether_addri, int> > map,
                         list<pair<uint16_t, bool> > values,
                         dchain indices,
                         ether_addri key);
  requires true;
  ensures map_has_fp(map, key) == dyn_table_has_key(gen_dyn_entries(map, values, indices), key);

  lemma void stat_map_has_get(list<pair<stat_keyi, uint16_t> > map, stat_keyi key);
  requires true == map_has_fp(map, key);
  ensures true == stat_table_has_key(gen_stat_entries(map), key) &*&
          map_get_fp(map, key) == stat_table_get(gen_stat_entries(map), key);

  lemma void dyn_map_has_get(list<pair<ether_addri, int> > map,
                             list<pair<uint16_t, bool> > values,
                             dchain indices,
                             ether_addri key);
  requires true == dyn_table_has_key(gen_dyn_entries(map, values, indices), key);
  ensures true == map_has_fp(map, key) &*&
          fst(nth(map_get_fp(map, key), values)) == dyn_table_get(gen_dyn_entries(map, values, indices), key);

  lemma void chain_out_of_space_ml_out_of_space(mapi<ether_addri> dyn_map,
                                                list<pair<uint16_t, bool> > vals,
                                                dchain indices,
                                                mapi<stat_keyi> stat_map);
  requires true;
  ensures dchain_out_of_space_fp(indices) ==
          dyn_table_out_of_space(bridge_abstract_function(dyn_map, vals, indices, stat_map));
@*/
