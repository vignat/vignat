#include <stdlib.h>
#include <string.h>

#include "double-chain.h"
#include "double-chain-impl.h"

//@ #include <nat.gh>
//@ #include "arith.gh"
//@ #include "stdex.gh"

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
        return alist != nil &&
               insync_fp(t, tstmps, tail(alist)) &&
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

  fixpoint list<pair<int, uint32_t> > dchain_alist_fp(dchain ch) {
    switch(ch) { case dchain(alist, size): return alist; }
  }
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

/*@
  lemma void insync_same_len(list<int> bare_alist,
                             list<int> tstmps,
                             list<pair<int, uint32_t> > alist)
  requires true == insync_fp(bare_alist, tstmps, alist);
  ensures length(alist) == length(bare_alist);
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        cons_head_tail(alist);
        insync_same_len(t, tstmps, tail(alist));
    }
  }

  lemma void insync_both_out_of_space(dchaini chi, dchain ch, list<int> tstmps)
  requires dchaini_irange_fp(chi) == dchain_index_range_fp(ch) &*&
           true == insync_fp(dchaini_alist_fp(chi), tstmps, dchain_alist_fp(ch));
  ensures dchaini_out_of_space_fp(chi) == dchain_out_of_space_fp(ch);
  {
    switch(ch) { case dchain(alist, size):
      switch(chi) { case dchaini(bare_alist, size1):
        insync_same_len(bare_alist, tstmps, alist);
        assert length(alist) == length(bare_alist);
        assert size == size1;
      }
    }
  }
  @*/

/*@
  lemma void extract_timestamp(uint32_t* arr, list<uint32_t> tstmps, int i)
  requires uints(arr, ?size, tstmps) &*& 0 <= i &*& i < size;
  ensures uints(arr, i, take(i, tstmps)) &*&
          u_integer(arr+i, nth(i, tstmps)) &*&
          uints(arr+i+1, size-i-1, drop(i+1, tstmps));
  {
    switch(tstmps) {
      case nil: return;
      case cons(h,t):
        open uints(arr, size, tstmps);
        if (i == 0) {
        } else {
          extract_timestamp(arr+1, t, i-1);
        }
        close uints(arr, i, take(i, tstmps));
    }
  }

  lemma void glue_timestamp(uint32_t* arr, list<uint32_t> tstmps, int i)
  requires 0 <= i &*& i < length(tstmps) &*&
           uints(arr, i, take(i, tstmps)) &*&
           u_integer(arr+i, nth(i, tstmps)) &*&
           uints(arr+i+1, length(tstmps)-i-1, drop(i+1, tstmps));
  ensures uints(arr, length(tstmps), tstmps);
  {
    switch(tstmps) {
      case nil: return;
      case cons(h,t):
        open uints(arr, i, take(i, tstmps));
        if (i == 0) {
        } else {
          glue_timestamp(arr+1, t, i-1);
        }
        close uints(arr, length(tstmps), tstmps);
    }
  }
  @*/

/*@
  lemma void dchaini_allocate_keep_irange(dchaini chi, int idx)
  requires true;
  ensures dchaini_irange_fp(chi) == dchaini_irange_fp(dchaini_allocate_fp(chi, idx));
  {
    switch(chi) { case dchaini(alist, size):
    }
  }

  lemma void dchain_allocate_keep_irange(dchain ch, int idx, uint32_t time)
  requires true;
  ensures dchain_index_range_fp(ch) ==
          dchain_index_range_fp(dchain_allocate_fp(ch, idx, time));
  {
    switch(ch) { case dchain(alist, size):
    }
  }
  @*/

/*@
  lemma void insync_append(list<int> bare_alist,
                           list<pair<int, uint32_t> > alist,
                           list<uint32_t> tstmps,
                           int ni, uint32_t nt)
  requires true == insync_fp(bare_alist, tstmps, alist) &*&
           0 <= ni &*& ni < length(tstmps) &*&
           false == mem(ni, bare_alist);
  ensures true == insync_fp(append(bare_alist, cons(ni, nil)),
                            update(ni, nt, tstmps),
                            append(alist, cons(pair(ni, nt), nil)));
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        insync_append(t, tail(alist), tstmps, ni, nt);
        cons_head_tail(alist);
        assert h != ni;
        nth_update_unrelevant(h, ni, nt, tstmps);
        assert alist != nil;
        append_nonnil_l(alist, cons(pair(ni, nt), nil));
    }
  }
  @*/

/*@
  lemma void dchaini_non_alloc_non_mem(dchaini dci, int i)
  requires true;
  ensures dchaini_allocated_fp(dci, i) == mem(i, dchaini_alist_fp(dci));
  {
    switch(dci) { case dchaini(alist, size):
    }
  }
  @*/

/*@
  lemma void dchaini_allocate_def(dchaini chi, int i)
  requires true;
  ensures append(dchaini_alist_fp(chi), cons(i, nil)) ==
          dchaini_alist_fp(dchaini_allocate_fp(chi, i));
  {
    switch(chi) { case dchaini(alist, size):
    }
  }
  @*/

/*@
  lemma void insync_mem_exists_same_index(list<int> bare_alist,
                                          list<pair<int, uint32_t> > alist,
                                          list<int> tstmps,
                                          int i)
  requires true == insync_fp(bare_alist, tstmps, alist);
  ensures mem(i, bare_alist) == exists(alist, (same_index)(i));
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        cons_head_tail(alist);
        insync_mem_exists_same_index(t, tail(alist), tstmps, i);
    }
  }

  lemma void dchain_allocated_def(dchain ch, int i)
  requires true;
  ensures dchain_allocated_fp(ch, i) ==
          exists(dchain_alist_fp(ch), (same_index)(i));
  {
    switch(ch) { case dchain(alist, size):
    }
  }
  @*/

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int *index_out, uint32_t time)
  /*@ requires double_chainp(?ch, chain) &*& *index_out |-> ?i; @*/
  /*@ ensures dchain_out_of_space_fp(ch) ?
               (result == 0 &*&
                *index_out |-> i &*&
                double_chainp(ch, chain)) :
               (result == 1 &*&
                *index_out |-> ?ni &*&
                false == dchain_allocated_fp(ch, ni) &*&
                0 <= ni &*& ni < dchain_index_range_fp(ch) &*&
                double_chainp(dchain_allocate_fp(ch, ni, time), chain)); @*/
{
  //@ open double_chainp(ch, chain);
  //@ assert chain->cells |-> ?cells;
  //@ assert chain->timestamps |-> ?timestamps;
  //@ assert dchainip(?chi, cells);
  //@ assert uints(timestamps, dchain_index_range_fp(ch), ?tstmps);
  //@ insync_both_out_of_space(chi, ch, tstmps);
  int ret = dchain_impl_allocate_new_index(chain->cells, index_out);
  //@ assert *index_out |-> ?ni;
  if (ret) {
    //@ extract_timestamp(timestamps, tstmps, ni);
    chain->timestamps[*index_out] = time;
    //@ take_update_unrelevant(ni, ni, time, tstmps);
    //@ drop_update_unrelevant(ni+1, ni, time, tstmps);
    //@ glue_timestamp(timestamps, update(ni, time, tstmps), ni);
    //@ dchaini_allocate_keep_irange(chi, ni);
    //@ dchain_allocate_keep_irange(ch, ni, time);
    //@ dchaini_non_alloc_non_mem(chi, ni);
    //@ insync_append(dchaini_alist_fp(chi), dchain_alist_fp(ch), tstmps, ni, time);
    //@ dchaini_allocate_def(chi, ni);
    //@ insync_mem_exists_same_index(dchaini_alist_fp(chi), dchain_alist_fp(ch), tstmps, ni);
    //@ dchain_allocated_def(ch, ni);
    //@ close double_chainp(dchain_allocate_fp(ch, ni, time), chain);
  } else {
    //@ close double_chainp(ch, chain);
  }
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
