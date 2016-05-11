#include <stdlib.h>
#include <string.h>

#include "double-chain.h"
#include "double-chain-impl.h"

//@ #include <nat.gh>
//@ #include "arith.gh"

struct DoubleChain {
  struct dchain_cell* cells;
  uint32_t *timestamps;
};

/*@

  fixpoint bool insync_fp(list<int> bare_alist, list<uint32_t> tstmps,
                          list<pair<int, uint32_t> > alist) {
    switch(bare_alist) {
      case nil: return alist == nil;
      case cons(h,t):
        return insync_fp(t, tstmps, tail(alist)) &&
               head(alist) == pair(h, nth(h, tstmps));
    }
  }

  predicate double_chainp(dchain ch,
                          struct DoubleChain* cp) =
      switch(ch) { case dchain(alist, index_range):
        return
          malloc_block_DoubleChain(cp) &*&
          cp->cells |-> ?cells &*&
          malloc_block_chars((void*)cells,
            (dchain_index_range_fp(ch)+DCHAIN_RESERVED)*
            sizeof(struct dchain_cell)) &*&
          cp->timestamps |-> ?timestamps &*&
          malloc_block_uints(timestamps, index_range) &*&
          uints(timestamps, index_range, ?tstamps) &*&
          dchainip(?dci, cells) &*&
          dchaini_irange_fp(dci) == index_range &*&
          true == insync_fp(dchaini_alist_fp(dci), tstamps, alist);
      };
  @*/

/*@
  lemma void bytes_to_dcell(void* dc)
  requires chars((void*)dc, sizeof(struct dchain_cell), ?chs);
  ensures dcellp(dc, _);
  {
    struct dchain_cell* dcp = dc;
    dcell_layout_assumptions(dcp);
    chars_split((void*)dc, sizeof(int));
    chars_to_integer((void*)&dcp->prev);
    chars_to_integer((void*)&dcp->next);
    close dchain_cell_prev(dc, _);
    close dchain_cell_next(dc, _);
  }

  lemma void bytes_to_dcells(void* dc, nat len)
  requires chars((void*)dc, int_of_nat(len)*sizeof(struct dchain_cell), ?chs);
  ensures dcellsp(dc, int_of_nat(len), _);
  {
    switch(len) {
      case zero:
        close dcellsp(dc, 0, nil);
        break;
      case succ(n):
        assert 1 <= int_of_nat(len);
        mul_mono(1, int_of_nat(len), sizeof(struct dchain_cell));
        assert sizeof(struct dchain_cell) <= int_of_nat(len)*sizeof(struct dchain_cell);
        chars_split(dc, sizeof(struct dchain_cell));
        assert int_of_nat(len)*sizeof(struct dchain_cell) - sizeof(struct dchain_cell) ==
               (int_of_nat(len)-1)*sizeof(struct dchain_cell);
        assert int_of_nat(len)-1 == int_of_nat(n);
        mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct dchain_cell));
        assert int_of_nat(len)*sizeof(struct dchain_cell) - sizeof(struct dchain_cell) ==
               int_of_nat(n)*sizeof(struct dchain_cell);
        bytes_to_dcells(dc+sizeof(struct dchain_cell), n);
        bytes_to_dcell(dc);
        close dcellsp(dc, int_of_nat(len), _);
    }
  }
  @*/

int dchain_allocate(int index_range, struct DoubleChain** chain_out)
  /*@ requires *chain_out |-> ?old_val &*&
               0 < index_range &*& index_range <= IRANG_LIMIT; @*/
  /*@ ensures result == 0 ?
               *chain_out |-> old_val :
               (result == 1 &*&
                *chain_out |-> ?chp &*&
                double_chainp(empty_dchain_fp(index_range), chp));
   @*/
{

  struct DoubleChain* old_chain_out = *chain_out;
  struct DoubleChain* chain_alloc = malloc(sizeof(struct DoubleChain));
  if (chain_alloc == NULL) return 0;
  *chain_out = (struct DoubleChain*) chain_alloc;

  //@ dcell_layout_assumptions((*chain_out)->cells);

  /*@
    mul_bounds(sizeof (struct dchain_cell), 1024,
               (index_range + DCHAIN_RESERVED), IRANG_LIMIT + DCHAIN_RESERVED);
    @*/
  struct dchain_cell* cells_alloc =
    malloc(sizeof (struct dchain_cell)*(index_range + DCHAIN_RESERVED));
  if (cells_alloc == NULL) {
    free(chain_alloc);
    *chain_out = old_chain_out;
    return 0;
  }
  (*chain_out)->cells = cells_alloc;

  uint32_t* timestamps_alloc = malloc(sizeof(uint32_t)*(index_range));
  if (timestamps_alloc == NULL) {
    free((void*)cells_alloc);
    free(chain_alloc);
    *chain_out = old_chain_out;
    return 0;
  }
  (*chain_out)->timestamps = timestamps_alloc;

  //@ bytes_to_dcells(cells_alloc, nat_of_int(index_range + DCHAIN_RESERVED));
  dchain_impl_init((*chain_out)->cells, index_range);
  //@ close double_chainp(empty_dchain_fp(index_range), chain_alloc);
  return 1;
}

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int *index_out, uint32_t time)
  /*@ requires double_chainp(?ch, chain) &*& *index_out |-> ?i; @*/
  /*@ ensures dchain_out_of_space_fp(ch) ?
    (result == 0 &*& *index_out |-> i &*&
    double_chainp(ch, chain)) :
    (result == 1 &*& *index_out |-> ?in &*&
    false == dchain_allocated_fp(ch, in) &*&
    0 <= in &*& in < dchain_index_range_fp(ch) &*&
    double_chainp(dchain_allocate_fp(ch, in, time), chain)); @*/
{
  int ret = dchain_impl_allocate_new_index(chain->cells, index_out);
  if (ret) chain->timestamps[*index_out] = time;
  return ret;
}

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
  0 <= index &*& index < dchain_index_range_fp(ch); @*/
/*@ ensures dchain_allocated_fp(ch, index) ?
  (result == 1 &*&
  double_chainp(dchain_rejuvenate_fp(ch, index, time), chain)) :
  (result == 0 &*&
  double_chainp(ch, chain)); @*/
{
  int ret = dchain_impl_rejuvenate_index(chain->cells, index);
  if (ret) {
    if (chain->timestamps[index] > time) return 0;
    chain->timestamps[index] = time;
  }
  return ret;
}

int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
 *index_out |-> ?io; @*/
/*@ ensures (dchain_is_empty_fp(ch) ?
  (double_chainp(ch, chain) &*&
  *index_out |-> io &*&
  result == 0) :
  (dchain_get_oldest_time_fp(ch) < time ?
  (*index_out |-> ?oi &*&
  dchain_get_oldest_index_fp(ch) == oi &*&
  double_chainp(dchain_remove_index_fp(ch, oi), chain) &*&
  result == 1) :
  (double_chainp(ch, chain) &*&
  *index_out |-> io &*&
  result == 0))); @*/
{
  int has_ind = dchain_impl_get_oldest_index(chain->cells, index_out);
  if (has_ind) {
    if (chain->timestamps[*index_out] < time) {
      return dchain_impl_free_index(chain->cells, *index_out);
    }
  }
  return 0;
}
