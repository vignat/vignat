#include "lib/bridge-abstract-state.h"


/*@

lemma void bridge_expire_abstract(list<pair<ether_addri, uint32_t> > dyn_map,
                                  list<pair<uint16_t, bool> > vals,
                                  list<pair<ether_addri, bool> > keys,
                                  dchain indices,
                                  time_t time)
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
{
  assume(false);//TODO
}
@*/
/*@

lemma void bridge_add_entry(list<pair<ether_addri, uint32_t> > dyn_map,
                            list<pair<uint16_t, bool> > vals,
                            dchain indices,
                            ether_addri addr,
                            uint32_t index,
                            uint16_t port,
                            time_t time)
requires true;
ensures set_eq(gen_dyn_entries(map_put_fp(dyn_map, addr, index),
                                update(index, pair(port, true), vals),
                                dchain_allocate_fp(indices, index, time)),
                add_dyn_entry(gen_dyn_entries(dyn_map, vals, indices),
                              addr, port, time)) == true;
{
  assume(false);//TODO
}

@*/
/*@
lemma void bridge_rejuv_entry(list<pair<ether_addri, uint32_t> > dyn_map,
                              list<pair<uint16_t, bool> > vals,
                              dchain indices,
                              ether_addri addr,
                              time_t time)
requires true;
ensures set_eq(gen_dyn_entries(dyn_map,
                                vals,
                                dchain_rejuvenate_fp(indices, map_get_fp(dyn_map, addr), time)),
                rejuvenate_dyn_entry(gen_dyn_entries(dyn_map, vals, indices),
                                    addr, time)) == true;
{
  assume(false);//TODO
}

@*/
/*@
lemma void bridge_rejuv_entry_set_eq(list<dyn_entry> dyn_table1,
                                      list<dyn_entry> dyn_table2,
                                      ether_addri addr,
                                      time_t time)
requires true == set_eq(dyn_table1, dyn_table2);
ensures true == set_eq(rejuvenate_dyn_entry(dyn_table1, addr, time),
                        rejuvenate_dyn_entry(dyn_table2, addr, time));
{
  assume(false);//TODO
}

@*/
/*@
lemma void bridge_add_entry_set_eq(list<dyn_entry> dyn_table1,
                                    list<dyn_entry> dyn_table2,
                                    ether_addri addr,
                                    uint16_t port,
                                    time_t time)
requires true == set_eq(dyn_table1, dyn_table2);
ensures true == set_eq(add_dyn_entry(dyn_table1, addr, port, time),
                        add_dyn_entry(dyn_table2, addr, port, time));
{
  assume(false);//TODO
}

@*/
/*@
lemma void stat_map_has(list<pair<stat_keyi, uint16_t> > map, stat_keyi key)
requires true;
ensures map_has_fp(map, key)== stat_table_has_key(gen_stat_entries(map), key);
{
  assume(false);//TODO
}
@*/
/*@
lemma void dyn_map_has(list<pair<ether_addri, int> > map,
                        list<pair<uint16_t, bool> > values,
                        dchain indices,
                        ether_addri key)
requires true;
ensures map_has_fp(map, key) == dyn_table_has_key(gen_dyn_entries(map, values, indices), key);
{
  assume(false);//TODO
}
@*/
/*@
lemma void stat_map_has_get(list<pair<stat_keyi, uint16_t> > map, stat_keyi key)
requires true == map_has_fp(map, key);
ensures true == stat_table_has_key(gen_stat_entries(map), key) &*&
        map_get_fp(map, key) == stat_table_get(gen_stat_entries(map), key);
{
  assume(false);//TODO
}

@*/
/*@
lemma void dyn_map_has_get(list<pair<ether_addri, int> > map,
                            list<pair<uint16_t, bool> > values,
                            dchain indices,
                            ether_addri key)
requires true == dyn_table_has_key(gen_dyn_entries(map, values, indices), key);
ensures true == map_has_fp(map, key) &*&
        fst(nth(map_get_fp(map, key), values)) == dyn_table_get(gen_dyn_entries(map, values, indices), key);
{
  assume(false);//TODO
}

@*/
/*@
lemma void chain_out_of_space_ml_out_of_space(mapi<ether_addri> dyn_map,
                                              list<pair<uint16_t, bool> > vals,
                                              dchain indices,
                                              mapi<stat_keyi> stat_map)
requires true;
ensures dchain_out_of_space_fp(indices) ==
        dyn_table_out_of_space(bridge_abstract_function(dyn_map, vals, indices, stat_map));
{
  assume(false);//TODO
}

@*/
