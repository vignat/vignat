#include "containers/double-chain-impl.h"

/*@
  lemma void dcell_layout_assumptions(struct dchain_cell* p)
  requires true;
  ensures sizeof(struct dchain_cell) == sizeof(int) + sizeof(int) &*&
  true == ((void*)&p->prev + sizeof(int) == (void*)&p->next);
  {
    assume(false);
  }
  @*/
