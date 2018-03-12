#include "containers/double-map.h"
#include "containers/double-chain.h"
#include "flow.h"
#include "coherence.h"
#include "bridge/bridge_data.h"

/*@
  inductive dyn_entry = dyn_entry(ether_addri, int);
  inductive stat_entry = stat_entry(stat_keyi, int);

  inductive ml_table = ml_table(list<dyn_entry>, list<stat_entry>, int);

  fixpoint list<dyn_entry> gen_dyn_entries(list<pair<ether_addri, uint8_t> > table) {
    switch(table) {
      case nil: return nil;
      case cons(h, t): return switch(h) { case pair(addr, index):
        return cons(dyn_entry(addr, index),
                    gen_dyn_entries(t));
      };
    }
  }

  fixpoint list<stat_entry> gen_stat_entries(list<pair<stat_keyi, uint8_t> > table) {
    switch(table) {
      case nil: return nil;
      case cons(h, t): return switch(h) { case pair(key, index):
        return cons(stat_entry(key, index),
                    gen_stat_entries(t));
      };
    }
  }

  fixpoint ml_table bridge_abstract_function(mapi<ether_addri> dyn_map,
                                             list<pair<uint8_t, bool> > vals,
                                             mapi<stat_keyi> stat_map) {
    switch(dyn_map) { case mapc(dyn_capacity, dm, daddrs):
      return switch(stat_map) { case mapc(stat_capacity, sm, saddrs):
        return ml_table(gen_dyn_entries(dm), gen_stat_entries(sm), dyn_capacity);
      };
    }
  }
  @*/
