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
      switch(ch) { case dchain(alist, index_range, low, high):
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
          true == insync_fp(dchaini_alist_fp(dci), tstamps, alist) &*&
          true == bnd_sorted_fp(map(snd, alist), low, high) &*&
          low <= high;
      };

  predicate dchain_is_sortedp(dchain ch) =
    switch(ch) { case dchain(alist, index_range, low, high):
      return true == bnd_sorted_fp(map(snd, alist), low, high);
    };

  predicate dchain_nodups(dchain ch) =
      true == distinct(dchain_indexes_fp(ch));


  fixpoint list<pair<int, uint32_t> > dchain_alist_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h): return alist; }
  }
  @*/

/*@
  fixpoint uint32_t dchain_low_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h): return l;}
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
                double_chainp(empty_dchain_fp(index_range, 0), chp));
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
  //@ close double_chainp(empty_dchain_fp(index_range, 0), chain_alloc);
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
    switch(ch) { case dchain(alist, size, l, h):
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

  lemma void allocate_preserves_index_range(dchain ch, int idx, uint32_t time)
  requires true;
  ensures dchain_index_range_fp(ch) ==
          dchain_index_range_fp(dchain_allocate_fp(ch, idx, time));
  {
    switch(ch) { case dchain(alist, size, l, h):
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
  lemma void dchaini_allocated_def(dchaini dci, int i)
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
    switch(ch) { case dchain(alist, size, l, h):
    }
  }
  @*/

/*@
  lemma void allocate_keeps_bnd_sorted(list<pair<int, uint32_t> > alist,
                                       int index,
                                       uint32_t low,
                                       uint32_t time,
                                       uint32_t high)
  requires true == bnd_sorted_fp(map(snd, alist), low, high) &*&
           high <= time &*&
           low <= high;
  ensures true == bnd_sorted_fp(map(snd, append(alist,
                                                cons(pair(index, time), nil))),
                                low, time);
  {
    switch(alist){
      case nil:
      case cons(h, t):
        allocate_keeps_bnd_sorted(t, index, snd(h), time, high);
    }
  }
  @*/

/*@
  lemma void allocate_keeps_high_bounded(dchain ch, int index, uint32_t time)
  requires dchain_high_fp(ch) <= time;
  ensures dchain_high_fp(dchain_allocate_fp(ch, index, time)) <= time;
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
    }
  }
  @*/

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int *index_out, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
             *index_out |-> ?i &*&
             dchain_high_fp(ch) <= time; @*/
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
    //@ allocate_preserves_index_range(ch, ni, time);
    //@ dchaini_allocated_def(chi, ni);
    //@ insync_append(dchaini_alist_fp(chi), dchain_alist_fp(ch), tstmps, ni, time);
    //@ dchaini_allocate_def(chi, ni);
    //@ insync_mem_exists_same_index(dchaini_alist_fp(chi), dchain_alist_fp(ch), tstmps, ni);
    //@ dchain_allocated_def(ch, ni);
    //@ allocate_keeps_bnd_sorted(dchain_alist_fp(ch), ni, dchain_low_fp(ch), time, dchain_high_fp(ch));
    //@ close double_chainp(dchain_allocate_fp(ch, ni, time), chain);
  } else {
    //@ close double_chainp(ch, chain);
  }
  return ret;
}

/*@
  lemma void dchaini_rejuvenate_keep_irange(dchaini chi, int idx)
  requires true;
  ensures dchaini_irange_fp(chi) ==
          dchaini_irange_fp(dchaini_rejuvenate_fp(chi, idx));
  {
    switch(chi) { case dchaini(alist, size):
    }
  }

  lemma void rejuvenate_preserves_index_range(dchain ch, int idx, uint32_t time)
  requires true;
  ensures dchain_index_range_fp(ch) ==
          dchain_index_range_fp(dchain_rejuvenate_fp(ch, idx, time));
  {
    switch(ch) { case dchain(alist, size, l, h):
    }
  }
  @*/

/*@
  lemma void dc_alist_no_dups(dchaini chi, int index)
  requires dchainip(chi, ?cells);
  ensures dchainip(chi, cells) &*&
          false == mem(index, remove(index, dchaini_alist_fp(chi)));
  {
    dchaini_no_dups(cells, chi, index);
    switch(chi) { case dchaini(alist, size):
    }
  }
  @*/

/*@
  lemma void insync_remove(list<int> bare_alist,
                           list<pair<int, uint32_t> > alist,
                           list<uint32_t> tstmps,
                           int i)
  requires true == insync_fp(bare_alist, tstmps, alist) &*&
           0 <= i &*& i < length(tstmps);
  ensures true == insync_fp(remove(i, bare_alist),
                            tstmps,
                            remove_by_index_fp(alist, i));
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        cons_head_tail(alist);
        insync_remove(t, tail(alist), tstmps, i);
    }
  }

  lemma void insync_rejuvenate(list<int> bare_alist,
                               list<pair<int, uint32_t> > alist,
                               list<uint32_t> tstmps,
                               int i, uint32_t t)
  requires true == insync_fp(bare_alist, tstmps, alist) &*&
           0 <= i &*& i < length(tstmps) &*&
           false == mem(i, remove(i, bare_alist));
  ensures true == insync_fp(append(remove(i, bare_alist), cons(i, nil)),
                            update(i, t, tstmps),
                            append(remove_by_index_fp(alist, i),
                                   cons(pair(i, t), nil)));
  {
    insync_remove(bare_alist, alist, tstmps, i);
    insync_append(remove(i, bare_alist),
                  remove_by_index_fp(alist, i), tstmps, i, t);
  }
  @*/

/*@
  lemma void rejuvenate_def(dchain dc, dchaini dci, int i, uint32_t t)
  requires true;
  ensures dchain_alist_fp(dchain_rejuvenate_fp(dc, i, t)) ==
          append(remove_by_index_fp(dchain_alist_fp(dc), i),
                 cons(pair(i,t), nil)) &*&
          dchaini_alist_fp(dchaini_rejuvenate_fp(dci, i)) ==
          append(remove(i, dchaini_alist_fp(dci)), cons(i, nil));
  {
    switch(dc) { case dchain(alist, size, l, h):
    }
    switch (dci) { case dchaini(alist, size):
    }
  }
  @*/

/*@
  lemma void get_time_int(list<int> bare_alist,
                          list<uint32_t> times,
                          list<pair<int, uint32_t> > alist,
                          int index)
  requires true == insync_fp(bare_alist, times, alist) &*&
           true == mem(index, bare_alist);
  ensures alist_get_fp(alist, index) == nth(index, times);
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        cons_head_tail(alist);
        if (h != index) get_time_int(t, times, tail(alist), index);
    }
  }
  @*/

/*@
  lemma void insync_update_unrelevant(list<int> bare_alist,
                                      list<uint32_t> times,
                                      list<pair<int, uint32_t> > alist,
                                      int i, uint32_t time)
  requires true == insync_fp(bare_alist, times, alist) &*&
           false == mem(i, bare_alist);
  ensures true == insync_fp(bare_alist, update(i, time, times), alist);
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        cons_head_tail(alist);
        insync_update_unrelevant(t, times, tail(alist), i, time);
        nth_update_unrelevant(h, i, time, times);
    }
  }
  @*/

/*@
  lemma void widen_bnd_sorted(list<uint32_t> times,
                              uint32_t l, uint32_t L,
                              uint32_t h, uint32_t H)
  requires true == bnd_sorted_fp(times, L, h) &*&
           l <= L &*& h <= H;
  ensures true == bnd_sorted_fp(times, l, H);
  {
    switch(times) {
      case nil: return;
      case cons(hd, tl):
        widen_bnd_sorted(tl, hd, hd, h, H);
    }
  }

  lemma void remove_index_keeps_bnd_sorted(list<pair<int, uint32_t> > alist,
                                           int index,
                                           uint32_t low,
                                           uint32_t high)
  requires true == bnd_sorted_fp(map(snd, alist), low, high);
  ensures true == bnd_sorted_fp(map(snd, remove_by_index_fp(alist, index)),
                                low, high);
  {
    switch(alist) {
      case nil: return;
      case cons(h, t):
        if (fst(h) == index) {
          widen_bnd_sorted(map(snd, t), low, snd(h), high, high);
        } else
          remove_index_keeps_bnd_sorted(t, index, snd(h), high);
    }
  }
  @*/

/*@
  lemma void remove_index_keeps_high_bounded(dchain ch, int index)
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          dchain_high_fp(dchain_remove_index_fp(ch, index)) <=
          dchain_high_fp(ch);
  {
    open double_chainp(ch, chain);
    switch(ch) { case dchain(alist, ir, lo, hi):
      remove_index_keeps_bnd_sorted(alist, index, lo, hi);
    }
    close double_chainp(ch, chain);
  }
  @*/

/*@
  lemma void rejuvenate_keeps_bnd_sorted(list<pair<int, uint32_t> > alist,
                                         int index,
                                         uint32_t low,
                                         uint32_t time,
                                         uint32_t high)
  requires true == bnd_sorted_fp(map(snd, alist), low, high) &*&
           high <= time &*&
           low <= high;
  ensures true == bnd_sorted_fp(map(snd, append(remove_by_index_fp(alist, index),
                                                cons(pair(index, time), nil))),
                                low, time);
  {
    remove_index_keeps_bnd_sorted(alist, index, low, high);
    allocate_keeps_bnd_sorted(remove_by_index_fp(alist, index), index,
                              low, time, high);
  }
  @*/

/*@
  lemma void rejuvenate_keeps_high_bounded(dchain ch, int index, uint32_t time)
  requires double_chainp(ch, ?chain) &*&
           dchain_high_fp(ch) <= time;
  ensures double_chainp(ch, chain) &*&
          dchain_high_fp(dchain_rejuvenate_fp(ch, index, time)) <= time;
  {
    open double_chainp(ch, chain);
    switch(ch) { case dchain(alist, ir, lo, hi):
      rejuvenate_keeps_bnd_sorted(alist, index, lo, time, hi);
    }
    close double_chainp(ch, chain);
  }
  @*/

/*@
  lemma void bnd_sorted_this_less_than_high(list<pair<int, uint32_t> > alist,
                                            int index,
                                            uint32_t low, uint32_t high)
  requires true == bnd_sorted_fp(map(snd, alist), low, high) &*&
           true == exists(alist, (same_index)(index));
  ensures alist_get_fp(alist, index) <= high;
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
      if (fst(h) != index)
        bnd_sorted_this_less_than_high(t, index, snd(h), high);
    }
  }
  @*/

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
             0 <= index &*& index < dchain_index_range_fp(ch) &*&
             dchain_high_fp(ch) <= time; @*/
/*@ ensures dchain_allocated_fp(ch, index) ?
             (dchain_get_time_fp(ch, index) <= time &*&
              result == 1 &*&
              double_chainp(dchain_rejuvenate_fp(ch, index, time), chain)) :
             (result == 0 &*&
              double_chainp(ch, chain)); @*/
{
  //@ open double_chainp(ch, chain);
  //@ assert chain->cells |-> ?cells;
  //@ assert chain->timestamps |-> ?timestamps;
  //@ assert dchainip(?chi, cells);
  //@ int size = dchain_index_range_fp(ch);
  //@ assert uints(timestamps, size, ?tmstmps);

  //@ dc_alist_no_dups(chi, index);
  int ret = dchain_impl_rejuvenate_index(chain->cells, index);
  //@ dchaini_allocated_def(chi, index);
  /*@ insync_mem_exists_same_index(dchaini_alist_fp(chi),
                                   dchain_alist_fp(ch), tmstmps, index);
                                   @*/
  //@ dchain_allocated_def(ch, index);
  if (ret) {
    //@ extract_timestamp(timestamps, tmstmps, index);
    chain->timestamps[index] = time;
    //@ take_update_unrelevant(index, index, time, tmstmps);
    //@ drop_update_unrelevant(index+1, index, time, tmstmps);
    //@ glue_timestamp(timestamps, update(index, time, tmstmps), index);
    /*@ {
      get_time_int(dchaini_alist_fp(chi),tmstmps, dchain_alist_fp(ch), index);
      switch(ch) { case dchain(alist, ir, lo, hi):
        bnd_sorted_this_less_than_high(alist, index, lo, hi);
      }
      assert dchain_get_time_fp(ch, index) <= time;
      dchaini_rejuvenate_keep_irange(chi, index);
      rejuvenate_preserves_index_range(ch, index, time);
      insync_rejuvenate(dchaini_alist_fp(chi), dchain_alist_fp(ch),
                        tmstmps, index, time);
      rejuvenate_def(ch, chi, index, time);
      rejuvenate_keeps_bnd_sorted(dchain_alist_fp(ch), index,
                                  dchain_low_fp(ch), time,
                                  dchain_high_fp(ch));
      close double_chainp(dchain_rejuvenate_fp(ch, index, time), chain);
      }@*/
  } else {
    /*@ {
      insync_update_unrelevant(dchaini_alist_fp(chi), tmstmps,
                               dchain_alist_fp(ch), index, time);
      close double_chainp(ch, chain);
      } @*/
  }
  return ret;
}

/*@
  lemma void get_oldest_index_def(dchain dc, dchaini dci)
  requires false == dchain_is_empty_fp(dc) &*&
           false == dchaini_is_empty_fp(dci);
  ensures dchain_get_oldest_index_fp(dc) == fst(head(dchain_alist_fp(dc))) &*&
          dchaini_get_oldest_index_fp(dci) == head(dchaini_alist_fp(dci));
  {
    switch(dc) { case dchain(alist, size, l, h):
    }
    switch(dci) { case dchaini(alist, size):
    }
  }
  @*/

/*@
  lemma void insync_head_matches(list<int> bare_alist,
                                 list<uint32_t> times,
                                 list<pair<int, uint32_t> > alist)
  requires true == insync_fp(bare_alist, times, alist) &*&
           bare_alist != nil;
  ensures fst(head(alist)) == head(bare_alist);
  {
    switch(bare_alist) {
      case nil:
        return;
      case cons(h,t): return;
    }
  }
  @*/

/*@
  lemma void is_empty_def(dchain dc, dchaini dci)
  requires true;
  ensures dchain_is_empty_fp(dc) == (dchain_alist_fp(dc) == nil) &*&
          dchaini_is_empty_fp(dci) == (dchaini_alist_fp(dci) == nil);
  {
    switch(dc) { case dchain(alist, size, l, h):
    }
    switch(dci) { case dchaini(alist, size):
    }
  }

  lemma void insync_both_empty(list<int> bare_alist,
                               list<uint32_t> times,
                               list<pair<int, uint32_t> > alist)
  requires true == insync_fp(bare_alist, times, alist);
  ensures bare_alist == nil ? (alist == nil) : (alist != nil);
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
    }
  }
  @*/

/*@
  lemma void remove_def(dchain dc, dchaini dci, int index)
  requires true;
  ensures dchain_alist_fp(dchain_remove_index_fp(dc, index)) ==
          remove_by_index_fp(dchain_alist_fp(dc), index) &*&
          dchaini_alist_fp(dchaini_remove_fp(dci, index)) ==
          remove(index, dchaini_alist_fp(dci)) &*&
          dchain_index_range_fp(dchain_remove_index_fp(dc, index)) ==
          dchain_index_range_fp(dc) &*&
          dchaini_irange_fp(dchaini_remove_fp(dci, index)) ==
          dchaini_irange_fp(dci);
  {
    switch(dc) { case dchain(alist, size, l, h):
    }
    switch(dci) { case dchaini(alist, size):
    }
  }
  @*/

/*@
  lemma void insync_get_oldest_time(dchain dc, dchaini dci,
                                    list<uint32_t> times)
  requires true == insync_fp(dchaini_alist_fp(dci),
                             times, dchain_alist_fp(dc)) &*&
           false == dchaini_is_empty_fp(dci);
  ensures nth(dchain_get_oldest_index_fp(dc), times) ==
          dchain_get_oldest_time_fp(dc);
  {
    switch(dc) { case dchain(alist, size, low, high):
      switch(dci) { case dchaini(bare_alist, sz):
        insync_both_empty(bare_alist, times, alist);
        switch(bare_alist) {
          case nil: return;
          case cons(h,t):
            cons_head_tail(alist);
            assert head(alist) == pair(h, nth(h, times));
        }
        assert dchain_get_oldest_index_fp(dc) == head(bare_alist);
      }
    }
  }
  @*/

int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
             *index_out |-> ?io; @*/
/*@ ensures (dchain_is_empty_fp(ch) ?
             (double_chainp(ch, chain) &*&
              *index_out |-> io &*&
              result == 0) :
              (*index_out |-> ?oi &*&
               dchain_get_oldest_index_fp(ch) == oi &*&
               0 <= oi &*& oi < dchain_index_range_fp(ch) &*&
               (dchain_get_oldest_time_fp(ch) < time ?
                (double_chainp(dchain_remove_index_fp(ch, oi), chain) &*&
                 result == 1) :
                (double_chainp(ch, chain) &*&
                 result == 0)))); @*/
{
  //@ open double_chainp(ch, chain);
  //@ assert chain->cells |-> ?cells;
  //@ assert chain->timestamps |-> ?timestamps;
  //@ assert dchainip(?chi, cells);
  //@ int size = dchain_index_range_fp(ch);
  //@ assert uints(timestamps, size, ?tmstmps);
  int has_ind = dchain_impl_get_oldest_index(chain->cells, index_out);
  //@ is_empty_def(ch, chi);
  //@ insync_both_empty(dchaini_alist_fp(chi), tmstmps, dchain_alist_fp(ch));
  //@ assert dchaini_is_empty_fp(chi) == dchain_is_empty_fp(ch);
  if (has_ind) {
    //@ get_oldest_index_def(ch, chi);
    //@ insync_head_matches(dchaini_alist_fp(chi), tmstmps, dchain_alist_fp(ch));
    //@ assert *index_out |-> ?oi;
    //@ insync_get_oldest_time(ch, chi, tmstmps);
    //@ extract_timestamp(timestamps, tmstmps, oi);
    if (chain->timestamps[*index_out] < time) {
      //@ glue_timestamp(timestamps, tmstmps, oi);
      //@ assert nth(oi, tmstmps) == dchain_get_oldest_time_fp(ch);
      int rez = dchain_impl_free_index(chain->cells, *index_out);
      /*@
        {
          assert rez == 1;
          remove_def(ch, chi, oi);
          insync_remove(dchaini_alist_fp(chi), dchain_alist_fp(ch),
                        tmstmps, oi);
          remove_index_keeps_bnd_sorted(dchain_alist_fp(ch), oi,
                                        dchain_low_fp(ch), dchain_high_fp(ch));
          close double_chainp(dchain_remove_index_fp(ch, oi), chain);
        }
        @*/
      return rez;
    }
    //@ glue_timestamp(timestamps, tmstmps, oi);
  }
  //@ close double_chainp(ch, chain);
  return 0;
}

/*@
  lemma void remove_by_index_decreases(list<pair<int, uint32_t> > alist,
                                       int i)
  requires true == exists(alist, (same_index)(i));
  ensures length(remove_by_index_fp(alist, i)) < length(alist);
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != i) {
          remove_by_index_decreases(t, i);
        }
    }
  }

  lemma void remove_by_index_monotone_len(list<pair<int, uint32_t> > alist,
                                          int i)
  requires true;
  ensures length(remove_by_index_fp(alist, i)) <= length(alist);
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (fst(h) == i) {
        } else {
          remove_by_index_monotone_len(t, i);
        }
    }
  }

  lemma void remove_some_monotone_len(list<pair<int, uint32_t> > alist,
                                      list<int> idx)
  requires true;
  ensures length(fold_left(alist, remove_by_index_fp, idx)) <= length(alist);
  {
    switch(idx) {
      case nil: return;
      case cons(h,t):
        remove_by_index_monotone_len(alist, h);
        remove_some_monotone_len(remove_by_index_fp(alist, h), t);
    }
  }

  lemma void remove_some_decreases_alist(list<pair<int, uint32_t> > alist,
                                         list<int> idx)
  requires idx == cons(?ih,_) &*& true == exists(alist, (same_index)(ih));
  ensures length(fold_left(alist, remove_by_index_fp, idx)) < length(alist);
  {
    switch(idx) {
      case nil: return;
      case cons(h,t):
        remove_by_index_decreases(alist, h);
        remove_some_monotone_len(remove_by_index_fp(alist, h), t);
    }
  }
  @*/

/*@
  lemma void mem_head_filter<t>(fixpoint (t,bool) pred, list<t> lst)
  requires filter(pred, lst) != nil;
  ensures true == mem(head(filter(pred, lst)), lst);
  {
    switch(lst) {
      case nil: return;
      case cons(h,t):
        if (pred(h)) {
        } else {
          mem_head_filter(pred, t);
        }
    }
  }
  @*/

/*@
  lemma void head_map<t,u>(fixpoint (t,u) f, list<t> lst)
  requires lst != nil;
  ensures head(map(f, lst)) == f(head(lst));
  {
    switch(lst) {
      case nil: return;
      case cons(h,t):
        return;
    }
  }
  @*/

/*@
  lemma void mem_exists_same_index(list<pair<int, uint32_t> > alist,
                                   pair<int, uint32_t> x)
  requires true == mem(x, alist);
  ensures true == exists(alist, (same_index)(fst(x)));
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (h != x) mem_exists_same_index(t, x);
    }
  }
  @*/

/*@
  lemma void head_expired_is_mem(list<pair<int, uint32_t> > alist, uint32_t time)
  requires get_expired_indexes_fp(time, alist) == cons(?eh,_);
  ensures true == exists(alist, (same_index)(eh));
  {
    list<pair<int, uint32_t> > exp = filter((is_cell_expired)(time), alist);
    mem_head_filter((is_cell_expired)(time), alist);
    assert(true == mem(head(exp), alist));
    head_map(fst, exp);
    assert(eh == fst(head(exp)));
    mem_exists_same_index(alist, head(exp));
  }
  @*/

/*@
  lemma void expire_old_dchain_nonfull(struct DoubleChain* chain, dchain ch,
                                       uint32_t time)
  requires double_chainp(ch, chain) &*&
           length(dchain_get_expired_indexes_fp(ch, time)) > 0;
  ensures double_chainp(ch, chain) &*&
          dchain_out_of_space_fp(dchain_expire_old_indexes_fp(ch, time)) ==
          false;
  {
    open double_chainp(ch, chain);
    assert chain->cells |-> ?cells;
    assert chain->timestamps |-> ?timestamps;
    assert dchainip(?chi, cells);
    int size = dchain_index_range_fp(ch);
    assert uints(timestamps, size, ?tmstmps);

    switch(ch) { case dchain(alist, sz, l, h):
      list<int> exp_inds = dchain_get_expired_indexes_fp(ch, time);
      assert exp_inds == get_expired_indexes_fp(time, alist);
      assert exp_inds != nil;
      switch(chi) { case dchaini(bare_alist, sz1):
        assert sz1 == sz;
        dchaini_alist_upperbound(cells, chi);
        assert length(bare_alist) <= sz1;
        insync_same_len(bare_alist, tmstmps, alist);
      }
      assert length(alist) <= size;
      cons_head_tail(exp_inds);
      head_expired_is_mem(alist, time);
      remove_some_decreases_alist(alist, exp_inds);
      assert length(fold_left(alist, remove_by_index_fp, exp_inds)) <
             length(alist);
    }

    close double_chainp(ch, chain);
  }
  @*/
/*@
  lemma void index_range_of_empty(int ir)
  requires 0 < ir;
  ensures dchain_index_range_fp(empty_dchain_fp(ir, 0)) == ir;
  {
  }

  lemma void expire_preserves_index_range(dchain ch, uint32_t time)
  requires true;
  ensures dchain_index_range_fp(dchain_expire_old_indexes_fp(ch, time)) ==
          dchain_index_range_fp(ch);
  {
    switch(ch) { case dchain(alist, size, l, h):
    }
  }
  @*/

/*@
  lemma void expire_indexes_tail(pair<int, uint32_t> ah,
                                 list<pair<int, uint32_t> > at,
                                 uint32_t time, int n)
  requires snd(ah) < time &*& 0 <= n;
  ensures fold_left(cons(ah,at), remove_by_index_fp,
                    take(n+1, get_expired_indexes_fp(time, cons(ah,at)))) ==
          fold_left(at, remove_by_index_fp,
                    take(n, get_expired_indexes_fp(time, at)));
  {
    switch(at) {
      case nil: return;
      case cons(h,t):
        if (0 < n)
          if (snd(h) < time)
            expire_indexes_tail(h, t, time, n-1);
    }
  }
  @*/

/*@
  lemma void all_new_no_expired_indexes(list<pair<int, uint32_t> > al,
                                        uint32_t time,
                                        uint32_t low, uint32_t high)
  requires true == bnd_sorted_fp(map(snd, al), low, high) &*&
           time <= low;
  ensures get_expired_indexes_fp(time, al) == nil;
  {
    switch(al) {
      case nil: return;
      case cons(h,t):
        all_new_no_expired_indexes(t, time, snd(h), high);
    }
  }
  @*/

/*@
  lemma void expire_n_plus_one_impl(list<pair<int, uint32_t> > al,
                                    uint32_t time, int n,
                                    uint32_t low, uint32_t high)
  requires fold_left(al, remove_by_index_fp,
                     take(n, get_expired_indexes_fp(time, al))) ==
           cons(?ah,?at) &*&
           snd(ah) < time &*&
           0 <= n &*&
           true == bnd_sorted_fp(map(snd, al), low, high);
  ensures fold_left(al, remove_by_index_fp,
                    take(n+1, get_expired_indexes_fp(time, al))) ==
          remove_by_index_fp(cons(ah, at), fst(ah)) &*&
          take(n+1, get_expired_indexes_fp(time, al)) ==
          append(take(n, get_expired_indexes_fp(time, al)),
                 cons(fst(ah), nil));
  {
    switch(al) {
      case nil:
        return;
      case cons(h,t):
        if (n != 0) {
          if (snd(h) < time) {
            expire_indexes_tail(h, t, time, n-1);
            assert fold_left(t, remove_by_index_fp,
                            take(n-1, get_expired_indexes_fp(time, t))) ==
                  cons(ah,at);
            expire_n_plus_one_impl(t, time, n-1, snd(h), high);
            expire_indexes_tail(h, t, time, n);
          } else {
            all_new_no_expired_indexes(al, time, snd(h), high);
          }
        }
    }
  }
  @*/
/*@
  lemma void double_chainp_to_sorted(dchain ch)
  requires double_chainp(ch, ?cp);
  ensures double_chainp(ch, cp) &*& dchain_is_sortedp(ch);
  {
    open double_chainp(ch, cp);
    close dchain_is_sortedp(ch);
    close double_chainp(ch, cp);
  }

  lemma void destroy_dchain_is_sortedp(dchain ch)
  requires dchain_is_sortedp(ch);
  ensures true;
  {
    open dchain_is_sortedp(ch);
  }
  @*/
/*@
  lemma void double_chain_alist_is_sorted(dchain ch)
  requires double_chainp(ch, ?cp);
  ensures double_chainp(ch, cp) &*&
          true == dchain_sorted_fp(ch);
  {
    open double_chainp(ch, cp);
    close double_chainp(ch, cp);
  }
  @*/

/*@
  lemma void expire_n_plus_one(dchain ch, uint32_t time, int n)
  requires false == dchain_is_empty_fp(expire_n_indexes(ch, time, n)) &*&
           dchain_get_oldest_time_fp(expire_n_indexes(ch, time, n)) <
           time &*&
           0 <= n &*&
           dchain_is_sortedp(ch);
  ensures dchain_remove_index_fp(expire_n_indexes(ch, time, n),
                                 dchain_get_oldest_index_fp
                                  (expire_n_indexes(ch, time, n))) ==
          expire_n_indexes(ch, time, n+1) &*&
          append(take(n, dchain_get_expired_indexes_fp(ch, time)),
                 cons(dchain_get_oldest_index_fp(expire_n_indexes(ch, time, n)),
                      nil)) ==
          take(n+1, dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_is_sortedp(ch);
  {
    open dchain_is_sortedp(ch);
    switch(ch) { case dchain(alist, ir, lo, hi):
      expire_n_plus_one_impl(alist, time, n, lo, hi);
    }
    close dchain_is_sortedp(ch);
  }
  @*/

/*@
  lemma void dchain_expired_indexes_limited(dchain ch, uint32_t time)
  requires double_chainp(ch, ?cp);
  ensures double_chainp(ch, cp) &*&
          length(dchain_get_expired_indexes_fp(ch, time)) <=
          dchain_index_range_fp(ch);
  {
    open double_chainp(ch, cp);
    assert dchainip(?dci, ?cells);
    switch(ch) { case dchain(alist, ir, lo, hi):
      dchaini_alist_upperbound(cp->cells, dci);
      assert uints(?timestamps, ir, ?tstmps);
      insync_same_len(dchaini_alist_fp(dci), tstmps, alist);
      assert length(alist) <= ir;
      filter_no_increase_len((is_cell_expired)(time), alist);
      map_preserves_length(fst, filter((is_cell_expired)(time), alist));
    }
    close double_chainp(ch, cp);
  }
  @*/

/*@
  lemma void alist_fst_exists(list<pair<int, uint32_t> > alist)
  requires alist == cons(?ah,?at);
  ensures true == exists(alist, (same_index)(fst(ah)));
  {
  }
  @*/

/*@
  lemma void dchain_oldest_allocated(dchain ch)
  requires false == dchain_is_empty_fp(ch);
  ensures true == dchain_allocated_fp(ch, dchain_get_oldest_index_fp(ch));
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
      alist_fst_exists(alist);
    }
  }
  @*/

/*@
  lemma void remove_by_index_len_monotonic(list<pair<int, uint32_t> > alist,
                                           int index)
  requires true;
  ensures length(remove_by_index_fp(alist, index)) <= length(alist) &*&
          length(alist) <= length(remove_by_index_fp(alist, index)) + 1;
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != index) remove_by_index_len_monotonic(t, index);
    }
  }
  @*/

/*@
  lemma void remove_all_idxes_eq_len(list<pair<int, uint32_t> > alist,
                                     list<int> lst)
  requires fold_left(alist, remove_by_index_fp, lst) == nil;
  ensures length(alist) <= length(lst);
  {
    switch(lst) {
      case nil: return ;
      case cons(h,t):
        remove_all_idxes_eq_len(remove_by_index_fp(alist, h), t);
        remove_by_index_len_monotonic(alist, h);
    }
  }
  @*/

/*@
  lemma void length_take_filter_same_filter_holey
              (list<pair<int, uint32_t> > alist,
               uint32_t time,
               int count)
  requires length(alist) <=
           length(take(count, map(fst, filter((is_cell_expired)(time),
                                              alist)))) &*&
           0 <= count;
  ensures length(alist) <= count &*& filter((is_cell_expired)(time),
                                            alist) == alist;
  {
    filter_effect_on_len(alist, (is_cell_expired)(time));
    map_effect_on_len(filter((is_cell_expired)(time), alist), fst);
    take_effect_on_len(map(fst, filter((is_cell_expired)(time), alist)),
                       count);
  }
  @*/

/*@
  lemma void all_cells_expired(list<pair<int, uint32_t> > alist,
                               uint32_t time, int count)
  requires fold_left(alist, remove_by_index_fp,
                     take(count, map(fst, filter((is_cell_expired)(time),
                                                 alist)))) ==
           nil &*&
           0 <= count;
  ensures filter((is_cell_expired)(time), alist) == alist &*&
          length(alist) <= count;
  {
    remove_all_idxes_eq_len(alist,
                            take(count, map(fst, filter((is_cell_expired)(time),
                                                        alist))));
    length_take_filter_same_filter_holey(alist, time, count);
  }
  @*/

/*@
  lemma void expired_indexes_limited2(list<pair<int, uint32_t> > alist,
                                      uint32_t time)
  requires true;
  ensures length(get_expired_indexes_fp(time, alist)) <= length(alist);
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        expired_indexes_limited2(t, time);
    }
  }
  @*/

/*@
  lemma void expired_all_impl(list<pair<int, uint32_t> > alist,
                              uint32_t time, int count)
  requires fold_left(alist, remove_by_index_fp,
                     take(count, map(fst, filter((is_cell_expired)(time),
                                                 alist)))) ==
           nil &*&
           0 <= count &*&
           count <= length(get_expired_indexes_fp(time, alist));
  ensures count == length(get_expired_indexes_fp(time, alist)) &*&
          get_expired_indexes_fp(time, alist) ==
          take(count, get_expired_indexes_fp(time, alist));
  {
     all_cells_expired(alist, time, count);
     expired_indexes_limited2(alist, time);
  }
  @*/

/*@
  lemma void expired_all(dchain ch, uint32_t time, int count)
  requires true == dchain_is_empty_fp(expire_n_indexes(ch, time, count)) &*&
           0 <= count &*&
           count <= length(dchain_get_expired_indexes_fp(ch, time));
  ensures count == length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_expire_old_indexes_fp(ch, time) ==
          expire_n_indexes(ch, time, count);
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
      expired_all_impl(alist, time, count);
    }
  }
  @*/

/*@
  lemma void sorted_expired_idxes_is_the_first_part
           (list<pair<int, uint32_t> > alist, uint32_t time,
            uint32_t low, uint32_t high)
  requires true == bnd_sorted_fp(map(snd, alist), low, high);
  ensures get_expired_indexes_fp(time, alist) ==
          map(fst, take(length(get_expired_indexes_fp(time, alist)), alist));
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (snd(h) < time) {
          sorted_expired_idxes_is_the_first_part(t, time, snd(h), high);
          cons_take_take_cons(h, t, length(get_expired_indexes_fp(time, alist))-1);
        } else {
          assert true == bnd_sorted_fp(map(snd, alist), snd(h), high);
          all_new_no_expired_indexes(alist, time, snd(h), high);
        }
    }
  }

  lemma void remove_first_indexes(list<pair<int, uint32_t> > alist, int n)
  requires 0 <= n;
  ensures fold_left(alist, remove_by_index_fp,
                    map(fst, take(n, alist))) == drop(n, alist);
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (0 < n) {
          remove_first_indexes(t, n-1);
        }
    }
  }

  @*/

/*@
  lemma void expired_indexes_are_old(list<pair<int, uint32_t> > alist,
                                     uint32_t time, int n,
                                     uint32_t low, uint32_t high)
  requires 0 <= n &*& n < length(get_expired_indexes_fp(time, alist)) &*&
           true == bnd_sorted_fp(map(snd, alist), low, high);
  ensures snd(nth(n, alist)) < time;
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (0 < n) {
          expired_indexes_are_old(t, time, n-1, snd(h), high);
        } else {
          if (time <= snd(h)) {
            all_new_no_expired_indexes(alist, time, snd(h), high);
            assert length(get_expired_indexes_fp(time, alist)) == 0;
          }
        }
    }
  }
  @*/

/*@
  lemma void no_more_expired_impl(list<pair<int, uint32_t> > alist,
                                  uint32_t time, int count,
                                  uint32_t low, uint32_t high)
  requires fold_left(alist, remove_by_index_fp,
                     take(count, get_expired_indexes_fp(time, alist))) ==
           cons(?ah,?at) &*&
           time <= snd(ah) &*&
           true == bnd_sorted_fp(map(snd, alist), low, high) &*&
           0 <= count;
  ensures length(get_expired_indexes_fp(time, alist)) <= count;
  {
    sorted_expired_idxes_is_the_first_part(alist, time, low, high);
    remove_first_indexes(alist, length(get_expired_indexes_fp(time, alist)));
    if (count < length(get_expired_indexes_fp(time, alist))) {
      take_effect_on_len(alist, length(get_expired_indexes_fp(time, alist)));
      expired_indexes_limited2(alist, time);
      take_map(count, fst,
               take(length(get_expired_indexes_fp(time, alist)), alist));
      take_take(count, length(get_expired_indexes_fp(time, alist)), alist);
      remove_first_indexes(alist, count);
      assert cons(ah,at) == drop(count, alist);
      car_drop_is_nth(count, alist);
      assert ah == nth(count, alist);
      expired_indexes_are_old(alist, time, count, low, high);
    }
  }
  @*/

/*@
  lemma void no_more_expired(dchain ch, uint32_t time, int count)
  requires false == dchain_is_empty_fp(expire_n_indexes(ch, time, count)) &*&
           time <=
           dchain_get_oldest_time_fp(expire_n_indexes(ch, time, count)) &*&
           0 <= count &*&
           count <= length(dchain_get_expired_indexes_fp(ch, time)) &*&
           dchain_is_sortedp(ch);
  ensures count == length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_expire_old_indexes_fp(ch, time) ==
          expire_n_indexes(ch, time, count) &*&
          dchain_is_sortedp(ch);
  {
    open dchain_is_sortedp(ch);
    switch(ch) { case dchain(alist, ir, lo, hi):
      no_more_expired_impl(alist, time, count, lo, hi);
    }
    close dchain_is_sortedp(ch);
  }
  @*/

/*@
  lemma void expired_indexes_exhausted(list<pair<int, uint32_t> > alist,
                                       uint32_t time,
                                       uint32_t low, uint32_t high)
  requires true == bnd_sorted_fp(map(snd, alist), low, high);
  ensures length(get_expired_indexes_fp(time, alist)) == length(alist) ?
            true :
            time <= snd(nth(length(get_expired_indexes_fp(time, alist)), alist));
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (time <= snd(h)) {
          all_new_no_expired_indexes(alist, time, snd(h), high);
          assert length(get_expired_indexes_fp(time, alist)) == 0;
        } else {
          expired_indexes_exhausted(t, time, snd(h), high);
        }
    }
  }
  @*/

/*@
  lemma void dchain_still_more_to_expire_impl(list<pair<int, uint32_t> > alist,
                                              uint32_t time, int count,
                                              uint32_t low, uint32_t high)
  requires fold_left(alist, remove_by_index_fp,
                     take(count, get_expired_indexes_fp(time, alist))) ==
           cons(?ah,?at) &*&
           snd(ah) < time &*&
           true == bnd_sorted_fp(map(snd, alist), low, high) &*&
           0 <= count;
  ensures count < length(get_expired_indexes_fp(time, alist));
  {
    list<int> expind = get_expired_indexes_fp(time, alist);
    take_effect_on_len(get_expired_indexes_fp(time, alist), count);
    if (length(expind) <= count) {
      expired_indexes_exhausted(alist, time, low, high);
      sorted_expired_idxes_is_the_first_part(alist, time, low, high);
      remove_first_indexes(alist, length(expind));
      take_take(length(expind), count, expind);
      if (length(expind) == length(alist)) {
      } else {
        expired_indexes_limited2(alist, time);
        car_drop_is_nth(length(expind), alist);

        assert time <= snd(ah);
      }
    }
  }
  @*/

/*@
  lemma void dchain_still_more_to_expire(dchain ch, uint32_t time, int count)
  requires false == dchain_is_empty_fp(expire_n_indexes(ch, time, count)) &*&
           dchain_get_oldest_time_fp(expire_n_indexes(ch, time, count)) <
           time &*&
           dchain_is_sortedp(ch) &*&
           0 <= count;
  ensures count < length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_is_sortedp(ch);
  {
    open dchain_is_sortedp(ch);
    switch(ch) { case dchain(alist, ri, lo, hi):
      dchain_still_more_to_expire_impl(alist, time, count, lo, hi);
    }
    close dchain_is_sortedp(ch);
  }
  @*/

/*@
  lemma void dchain_indexes_contain_idx_impl(list<pair<int, uint32_t> > alist,
                                             int idx)
  requires true;
  ensures exists(alist, (same_index)(idx)) == mem(idx, map(fst, alist));
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != idx) dchain_indexes_contain_idx_impl(t, idx);
    }
  }
  @*/

/*@
  lemma void dchain_indexes_contain_index(dchain ch, int idx)
  requires true;
  ensures dchain_allocated_fp(ch, idx) == mem(idx, dchain_indexes_fp(ch));
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
      dchain_indexes_contain_idx_impl(alist, idx);
    }
  }
  @*/

/*@
  lemma void dchain_remove_keeps_ir(dchain ch, int idx)
  requires true;
  ensures dchain_index_range_fp(ch) ==
          dchain_index_range_fp(dchain_remove_index_fp(ch, idx));
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
    }
  }
  @*/

/*@
  lemma void dchain_remove_idx_from_indexes_impl
              (list<pair<int, uint32_t> > alist, int idx)
  requires true;
  ensures map(fst, remove_by_index_fp(alist, idx)) ==
          remove(idx, map(fst, alist));
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != idx) dchain_remove_idx_from_indexes_impl(t, idx);
    }
  }
  @*/

/*@
  lemma void dchain_remove_idx_from_indexes(dchain ch, int idx)
  requires true;
  ensures dchain_indexes_fp(dchain_remove_index_fp(ch, idx)) ==
          remove(idx, dchain_indexes_fp(ch));
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
      dchain_remove_idx_from_indexes_impl(alist, idx);
    }
  }
  @*/

/*@
  lemma void dchain_nodups_unique_idx(dchain ch, int idx)
  requires dchain_nodups(ch);
  ensures false == mem(idx, remove(idx, dchain_indexes_fp(ch))) &*&
          dchain_nodups(ch);
  {
    open dchain_nodups(ch);
    switch(ch) { case dchain(alist, ir, lo, hi):
      distinct_unique(map(fst, alist), idx);
    }
    close dchain_nodups(ch);
  }
  @*/

/*@
  lemma void dchain_remove_keeps_nodups(dchain ch, int idx)
  requires dchain_nodups(ch);
  ensures dchain_nodups(dchain_remove_index_fp(ch, idx));
  {
    open dchain_nodups(ch);
    dchain_remove_idx_from_indexes(ch, idx);
    distinct_remove(idx, dchain_indexes_fp(ch));
    close dchain_nodups(dchain_remove_index_fp(ch, idx));
  }
  @*/

/*@
  lemma void indexes_is_dci_alist(list<pair<int, uint32_t> > alist,
                                  list<uint32_t> tstamps,
                                  list<int> bare_alist)
  requires true == insync_fp(bare_alist, tstamps, alist);
  ensures map(fst, alist) == bare_alist;
  {
    switch(bare_alist) {
      case nil: return;
      case cons(h,t):
        indexes_is_dci_alist(tail(alist), tstamps, t);
        cons_head_tail(alist);
    }
  }
  @*/

/*@
  lemma void mem_remove_drop<t>(list<t> l, int i, t x, t y)
  requires false == mem(y, remove(x, l)) &*& 0 <= i;
  ensures false == mem(y, remove(x, drop(i, l)));
  {
    switch(l) {
      case nil: return;
      case cons(h,t):
        if (0 < i) {
          if (mem(y, remove(x, t))) {
            mem_remove_mem(y, x, t);
          }
          mem_remove_drop(t, i-1, x, y);
        }
    }
  }
  @*/

/*@
  lemma void dchaini_alist_distinct(dchaini chi)
  requires dchainip(chi, ?cells);
  ensures dchainip(chi, cells) &*&
          true == distinct(dchaini_alist_fp(chi));
  {
    list<int> alist = dchaini_alist_fp(chi);
    int i = length(alist);
    while (0 < i)
      invariant dchainip(chi, cells) &*& 0 <= i &*& i <= length(alist) &*&
                true == distinct(drop(i, alist));
      decreases i;
    {
      int cur = nth(i-1, alist);
      dc_alist_no_dups(chi, cur);
      list<int> next = drop(i-1, alist);
      drop_cons(alist, i-1);
      assert next == cons(cur, drop(i, alist));
      assert false == mem(cur, remove(cur, alist));
      mem_remove_drop(alist, i-1, cur, cur);
      assert false == mem(cur, remove(cur, drop(i-1, alist)));
      assert remove(cur, drop(i-1, alist)) == drop(i, alist);
      --i;
    }
    assert true == distinct(alist);
  }
  @*/

/*@
  lemma void double_chain_nodups(dchain ch)
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          dchain_nodups(ch);
  {
    open double_chainp(ch, chain);
    assert dchainip(?chi, ?cells);
    assert uints(_, _, ?tstamps);
    switch(ch) { case dchain(alist, ir, lo, hi):
      indexes_is_dci_alist(alist, tstamps, dchaini_alist_fp(chi));
    }
    dchaini_alist_distinct(chi);
    close double_chainp(ch, chain);
    close dchain_nodups(ch);
  }
  @*/

/*@
  lemma void dchain_distinct_indexes(dchain ch)
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          true == distinct(dchain_indexes_fp(ch));
  {
    open double_chainp(ch, chain);
    assert dchainip(?chi, ?cells);
    assert uints(_, _, ?tstamps);
    switch(ch) { case dchain(alist, ir, lo, hi):
      indexes_is_dci_alist(alist, tstamps, dchaini_alist_fp(chi));
    }
    dchaini_alist_distinct(chi);
    close double_chainp(ch, chain);
  }
  @*/

/*@
  lemma void destroy_dchain_nodups(dchain ch)
  requires dchain_nodups(ch);
  ensures true;
  {
    open dchain_nodups(ch);
  }
  @*/

/*@
  lemma void remove_by_index_to_remove(list<pair<int, uint32_t> > alist,
                                       int index)
  requires true;
  ensures map(fst, remove_by_index_fp(alist, index)) ==
          remove(index, map(fst, alist));
  {
    switch(alist) {
      case nil: return;
      case cons(h,t):
        if (fst(h) != index) remove_by_index_to_remove(t, index);
    }
  }
  @*/

/*@

  lemma void dchain_rejuvenate_indexes_subset
               (list<pair<int, uint32_t> > alist, int index, uint32_t time)
  requires true;
  ensures true == subset(map(fst, alist),
                         map(fst, append(remove_by_index_fp(alist, index),
                                         cons(pair(index, time), nil))));
  {
    remove_by_index_to_remove(alist, index);
    map_append(fst, remove_by_index_fp(alist, index),
               cons(pair(index, time), nil));
    assert(map(fst, append(remove_by_index_fp(alist, index),
                           cons(pair(index, time), nil))) ==
           append(remove(index, map(fst, alist)), cons(index, nil)));
    subset_push_to_the_end(map(fst, alist),
                           map(fst, alist),
                           index);
  }

  lemma void dchain_rejuvenate_indexes_superset
               (list<pair<int, uint32_t> > alist, int index, uint32_t time)
  requires true == mem(index, map(fst, alist));
  ensures true == subset(map(fst, append(remove_by_index_fp(alist, index),
                                         cons(pair(index, time), nil))),
                         map(fst, alist));
  {
    remove_by_index_to_remove(alist, index);
    map_append(fst, remove_by_index_fp(alist, index),
               cons(pair(index, time), nil));
    push_to_the_end_subset(map(fst, alist), map(fst, alist), index);
  }

lemma void dchain_rejuvenate_preserves_indexes_set(dchain ch, int index,
                                                   uint32_t time)
requires true == dchain_allocated_fp(ch, index);
ensures true == subset(dchain_indexes_fp(ch),
                       dchain_indexes_fp(dchain_rejuvenate_fp(ch, index,
                                                              time))) &*&
        true == subset(dchain_indexes_fp(dchain_rejuvenate_fp(ch, index,
                                                              time)),
                       dchain_indexes_fp(ch));
{
  dchain_indexes_contain_index(ch, index);
  switch(ch) { case dchain(alist, ir, lo, hi):
    dchain_rejuvenate_indexes_subset(alist, index, time);
    dchain_rejuvenate_indexes_superset(alist, index, time);
  }
}

@*/


/*@
  lemma void dchain_allocate_append_to_indexes_impl
               (list<pair<int, uint32_t> > alist,
                int ind, uint32_t time)
  requires true;
  ensures map(fst, append(alist, cons(pair(ind, time), nil))) ==
          append(map(fst, alist), cons(ind, nil));
  {
    map_append(fst, alist, cons(pair(ind, time), nil));
  }
  @*/

/*@
  lemma void dchain_allocate_append_to_indexes(dchain ch, int ind, uint32_t time)
  requires true;
  ensures dchain_indexes_fp(dchain_allocate_fp(ch, ind, time)) ==
          append(dchain_indexes_fp(ch), cons(ind, nil));
  {
    switch(ch) { case dchain(alist, ir, lo, hi):
      dchain_allocate_append_to_indexes_impl(alist, ind, time);
    }
  }
  @*/

/*@
  lemma void expire_olds_keeps_high_bounded(dchain ch, uint32_t time)
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          dchain_high_fp(dchain_expire_old_indexes_fp(ch, time)) <=
          dchain_high_fp(ch);
  {
    switch(ch) { case dchain(alist, ir, lo, hi) :
    }
  }
  @*/
