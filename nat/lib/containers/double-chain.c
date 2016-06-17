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

  fixpoint bool bnd_sorted_fp(list<uint32_t> times,
                              uint32_t low, uint32_t high) {
    switch(times) {
      case nil: return true;
      case cons(h,t):
        return low <= h && h <= high &&
               bnd_sorted_fp(t, h, high);
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

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
             0 <= index &*& index < dchain_index_range_fp(ch) &*&
             dchain_high_fp(ch) <= time; @*/
/*@ ensures dchain_allocated_fp(ch, index) ?
             (dchain_get_time_fp(ch, index) < time ?
              (result == 1 &*&
               double_chainp(dchain_rejuvenate_fp(ch, index, time), chain)) :
              (result == 0 &*&
               double_chainp(ch, chain))) :
             (result == 0 &*&
              double_chainp(ch, chain)); @*/
{
  //@ open double_chainp(ch, chain);
  //@ assert chain->cells |-> ?cells;
  //@ assert chain->timestamps |-> ?timestamps;
  //@ assert dchainip(?chi, cells);
  //@ int size = dchain_index_range_fp(ch);
  //@ assert uints(timestamps, size, ?tmstmps);
  //@ extract_timestamp(timestamps, tmstmps, index);

  /* Checking the timestamp is safe,
     even if the index is not really allocated */
  if (chain->timestamps[index] < time) {
    //@ assert nth(index, tmstmps) < time;
    chain->timestamps[index] = time;
    //@ take_update_unrelevant(index, index, time, tmstmps);
    //@ drop_update_unrelevant(index+1, index, time, tmstmps);
    //@ glue_timestamp(timestamps, update(index, time, tmstmps), index);
    //@ dc_alist_no_dups(chi, index);
    int ret = dchain_impl_rejuvenate_index(chain->cells, index);
    //@ dchaini_allocated_def(chi, index);
    /*@ insync_mem_exists_same_index(dchaini_alist_fp(chi),
                                     dchain_alist_fp(ch), tmstmps, index);
                                     @*/
    //@ dchain_allocated_def(ch, index);
    /*@
      if (ret) {
        get_time_int(dchaini_alist_fp(chi),tmstmps, dchain_alist_fp(ch), index);
        assert dchain_get_time_fp(ch, index) < time;
        dchaini_rejuvenate_keep_irange(chi, index);
        rejuvenate_preserves_index_range(ch, index, time);
        insync_rejuvenate(dchaini_alist_fp(chi), dchain_alist_fp(ch),
                          tmstmps, index, time);
        rejuvenate_def(ch, chi, index, time);
        rejuvenate_keeps_bnd_sorted(dchain_alist_fp(ch), index,
                                     dchain_low_fp(ch), time,
                                     dchain_high_fp(ch));
        close double_chainp(dchain_rejuvenate_fp(ch, index, time), chain);
      } else {
        insync_update_unrelevant(dchaini_alist_fp(chi), tmstmps,
                                 dchain_alist_fp(ch), index, time);
        close double_chainp(ch, chain);
      }
      @*/
    return ret;
  }
  //@ glue_timestamp(timestamps, tmstmps, index);
  /*@
    if (dchain_allocated_fp(ch, index)) {
      dchain_allocated_def(ch, index);
      insync_mem_exists_same_index(dchaini_alist_fp(chi), dchain_alist_fp(ch),
                                   tmstmps, index);
      get_time_int(dchaini_alist_fp(chi), tmstmps, dchain_alist_fp(ch), index);
      assert time <= dchain_get_time_fp(ch, index);
    }
    @*/
  //@ close double_chainp(ch, chain);
  return 0;
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
