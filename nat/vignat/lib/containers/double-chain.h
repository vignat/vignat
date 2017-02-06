#ifndef _DOUBLE_CHAIN_H_INCLUDED_
#define _DOUBLE_CHAIN_H_INCLUDED_

#include <stdint.h>

//@ #include <listex.gh>
//@ #include "stdex.gh"

struct DoubleChain;
/* Makes sure the allocator structur fits into memory, and particularly into
   32 bit address space. @*/
#define IRANG_LIMIT (1048576)

/*@
  inductive dchain = dchain(list<pair<int, uint32_t> >, int,
                            uint32_t, uint32_t);

  predicate double_chainp(dchain ch,
                          struct DoubleChain* cp);

  predicate dchain_is_sortedp(dchain ch);
  predicate dchain_nodups(dchain ch);

  fixpoint dchain empty_dchain_fp(int index_range, uint32_t low) {
    return dchain(nil, index_range, low, low);
  }

  fixpoint bool dchain_out_of_space_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, low, high):
      return size <= length(alist);
    }
  }

  fixpoint int dchain_index_range_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h): return size; }
  }

  fixpoint list<int> dchain_indexes_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h): return map(fst, alist); }
  }

  fixpoint uint32_t dchain_high_fp(dchain ch) {
    switch(ch) {case dchain(alist, size, l, h): return h;}
  }

  fixpoint bool same_index(int i, pair<int, uint32_t> b) {
    return i == fst(b);
  }

  fixpoint bool dchain_allocated_fp(dchain ch, int index) {
    switch(ch) { case dchain(alist, size, l, h):
      return exists(alist, (same_index)(index));
    }
  }

  fixpoint dchain dchain_allocate_fp(dchain ch, int index, uint32_t t) {
    switch(ch) { case dchain(alist, size, l, h):
      return dchain(append(alist, cons(pair(index, t), nil)), size,
                    l, t);
    }
  }

  fixpoint list<pair<int, uint32_t> >
    remove_by_index_fp(list<pair<int, uint32_t> > lst, int i) {
      switch(lst) {
        case nil: return nil;
        case cons(h,t):
          return fst(h) == i ? t :
                               cons(h, remove_by_index_fp(t, i));
      }
    }

  fixpoint dchain dchain_rejuvenate_fp(dchain ch, int index, uint32_t time) {
    switch(ch) { case dchain(alist, size, l, h):
      return dchain(append(remove_by_index_fp(alist, index),
                           cons(pair(index, time), nil)),
                    size,
                    l, time);
    }
  }

  fixpoint uint32_t alist_get_fp(list<pair<int, uint32_t> > al, int i) {
    switch(al) {
      case nil: return default_value<uint32_t>();
      case cons(h,t):
        return (fst(h) == i) ? snd(h) : alist_get_fp(t, i);
    }
  }

  fixpoint uint32_t dchain_get_time_fp(dchain ch, int index) {
    switch(ch) { case dchain(alist, size, l, h):
      return alist_get_fp(alist, index);
    }
  }

  fixpoint bool dchain_is_empty_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h):
      return alist == nil;
    }
  }

  fixpoint int dchain_get_oldest_index_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h):
      return fst(head(alist));
    }
  }

  fixpoint uint32_t dchain_get_oldest_time_fp(dchain ch) {
    switch(ch) { case dchain(alist, size, l, h):
      return snd(head(alist));
    }
  }

  fixpoint dchain dchain_remove_index_fp(dchain ch, int index) {
    switch(ch) { case dchain(alist, size, l, h):
      return dchain(remove_by_index_fp(alist, index), size, l, h);
    }
  }

  fixpoint bool is_cell_expired(uint32_t time, pair<int, uint32_t> cell) {
    return snd(cell) < time;
  }

  fixpoint list<int>
  get_expired_indexes_fp(uint32_t time, list<pair<int, uint32_t> > lst) {
    return map(fst, filter((is_cell_expired)(time), lst));
  }

  fixpoint list<int> dchain_get_expired_indexes_fp(dchain ch, uint32_t time) {
    switch(ch) { case dchain(alist, size, l, h):
      return get_expired_indexes_fp(time, alist);
    }
  }

  fixpoint dchain dchain_expire_old_indexes_fp(dchain ch, uint32_t time) {
    switch(ch) { case dchain(alist, size, l, h):
      return dchain(fold_left(alist, remove_by_index_fp,
                              get_expired_indexes_fp(time, alist)),
                    size,
                    l, h);
    }
  }

  fixpoint dchain expire_n_indexes(dchain ch, uint32_t time, int n) {
    switch(ch) { case dchain(alist, size, l, h):
      return dchain(fold_left(alist, remove_by_index_fp,
                              take(n, get_expired_indexes_fp(time, alist))),
                    size,
                    l, h);
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

  fixpoint bool dchain_sorted_fp(dchain ch) {
    switch(ch) { case dchain(alist, index_range, low, high):
      return bnd_sorted_fp(map(snd, alist), low, high);
    }
  }


  lemma void expire_old_dchain_nonfull(struct DoubleChain* chain, dchain ch,
                                       uint32_t time);
  requires double_chainp(ch, chain) &*&
           length(dchain_get_expired_indexes_fp(ch, time)) > 0;
  ensures double_chainp(ch, chain) &*&
          dchain_out_of_space_fp(dchain_expire_old_indexes_fp(ch, time)) ==
          false;

  lemma void index_range_of_empty(int ir, uint32_t l);
  requires 0 < ir;
  ensures dchain_index_range_fp(empty_dchain_fp(ir, l)) == ir;

  lemma void expire_preserves_index_range(dchain ch, uint32_t time);
  requires true;
  ensures dchain_index_range_fp(dchain_expire_old_indexes_fp(ch, time)) ==
          dchain_index_range_fp(ch);

  lemma void rejuvenate_preserves_index_range(dchain ch, int index,
                                              uint32_t time);
  requires true;
  ensures dchain_index_range_fp(dchain_rejuvenate_fp(ch, index, time)) ==
          dchain_index_range_fp(ch);

  lemma void allocate_preserves_index_range(dchain ch, int index, uint32_t t);
  requires true;
  ensures dchain_index_range_fp(dchain_allocate_fp(ch, index, t)) ==
          dchain_index_range_fp(ch);

  lemma void double_chainp_to_sorted(dchain ch);
  requires double_chainp(ch, ?cp);
  ensures double_chainp(ch, cp) &*& dchain_is_sortedp(ch);

  lemma void double_chain_alist_is_sorted(dchain ch);
  requires double_chainp(ch, ?cp);
  ensures double_chainp(ch, cp) &*&
          true == dchain_sorted_fp(ch);

  lemma void destroy_dchain_is_sortedp(dchain ch);
  requires dchain_is_sortedp(ch);
  ensures true;

  lemma void expire_n_plus_one(dchain ch, uint32_t time, int n);
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

  lemma void dchain_expired_indexes_limited(dchain ch, uint32_t time);
  requires double_chainp(ch, ?cp);
  ensures double_chainp(ch, cp) &*&
          length(dchain_get_expired_indexes_fp(ch, time)) <=
          dchain_index_range_fp(ch);

  lemma void dchain_oldest_allocated(dchain ch);
  requires false == dchain_is_empty_fp(ch);
  ensures true == dchain_allocated_fp(ch, dchain_get_oldest_index_fp(ch));

  lemma void expired_all(dchain ch, uint32_t time, int count);
  requires true == dchain_is_empty_fp(expire_n_indexes(ch, time, count)) &*&
           0 <= count &*&
           count <= length(dchain_get_expired_indexes_fp(ch, time));
  ensures count == length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_expire_old_indexes_fp(ch, time) ==
          expire_n_indexes(ch, time, count);

  lemma void no_more_expired(dchain ch, uint32_t time, int count);
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


  lemma void dchain_still_more_to_expire(dchain ch, uint32_t time, int count);
  requires false == dchain_is_empty_fp(expire_n_indexes(ch, time, count)) &*&
           dchain_get_oldest_time_fp(expire_n_indexes(ch, time, count)) <
           time &*&
           dchain_is_sortedp(ch) &*&
           0 <= count;
  ensures count < length(dchain_get_expired_indexes_fp(ch, time)) &*&
          dchain_is_sortedp(ch);

  lemma void dchain_indexes_contain_index(dchain ch, int idx);
  requires true;
  ensures dchain_allocated_fp(ch, idx) == mem(idx, dchain_indexes_fp(ch));
  @*/

/*@
  lemma void dchain_remove_keeps_ir(dchain ch, int idx);
  requires true;
  ensures dchain_index_range_fp(ch) ==
          dchain_index_range_fp(dchain_remove_index_fp(ch, idx));

  lemma void dchain_remove_idx_from_indexes(dchain ch, int idx);
  requires true;
  ensures dchain_indexes_fp(dchain_remove_index_fp(ch, idx)) ==
          remove(idx, dchain_indexes_fp(ch));

  lemma void dchain_nodups_unique_idx(dchain ch, int idx);
  requires dchain_nodups(ch);
  ensures false == mem(idx, remove(idx, dchain_indexes_fp(ch))) &*&
          dchain_nodups(ch);

  lemma void dchain_remove_keeps_nodups(dchain ch, int idx);
  requires dchain_nodups(ch);
  ensures dchain_nodups(dchain_remove_index_fp(ch, idx));

  lemma void destroy_dchain_nodups(dchain ch);
  requires dchain_nodups(ch);
  ensures true;

  lemma void double_chain_nodups(dchain ch);
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          dchain_nodups(ch);

  lemma void dchain_distinct_indexes(dchain ch);
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          true == distinct(dchain_indexes_fp(ch));

  lemma void dchain_rejuvenate_preserves_indexes_set(dchain ch, int index,
                                                     uint32_t time);
  requires true == dchain_allocated_fp(ch, index);
  ensures true == subset(dchain_indexes_fp(ch),
                        dchain_indexes_fp(dchain_rejuvenate_fp(ch, index,
                                                                time))) &*&
          true == subset(dchain_indexes_fp(dchain_rejuvenate_fp(ch, index,
                                                                time)),
                        dchain_indexes_fp(ch));
  lemma void dchain_allocate_append_to_indexes(dchain ch, int ind,
                                               uint32_t time);
  requires true;
  ensures dchain_indexes_fp(dchain_allocate_fp(ch, ind, time)) ==
          append(dchain_indexes_fp(ch), cons(ind, nil));

  lemma void allocate_keeps_high_bounded(dchain ch, int index, uint32_t time);
  requires dchain_high_fp(ch) <= time;
  ensures dchain_high_fp(dchain_allocate_fp(ch, index, time)) <= time;

  lemma void rejuvenate_keeps_high_bounded(dchain ch, int index, uint32_t time);
  requires double_chainp(ch, ?chain) &*&
           dchain_high_fp(ch) <= time;
  ensures double_chainp(ch, chain) &*&
          dchain_high_fp(dchain_rejuvenate_fp(ch, index, time)) <= time;

  lemma void remove_index_keeps_high_bounded(dchain ch, int index);
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          dchain_high_fp(dchain_remove_index_fp(ch, index)) <=
          dchain_high_fp(ch);

  lemma void expire_olds_keeps_high_bounded(dchain ch, uint32_t time);
  requires double_chainp(ch, ?chain);
  ensures double_chainp(ch, chain) &*&
          dchain_high_fp(dchain_expire_old_indexes_fp(ch, time)) <=
          dchain_high_fp(ch);
  @*/

/**
   Allocate memory and initialize a new double chain allocator. The produced
   allocator will operate on indexes [0-index).

   @param index_range - the limit on the number of allocated indexes.
   @param chain_out - an output pointer that will hold the pointer to the newly
                      allocated allocator in the case of success.
   @returns 0 if the allocation failed, and 1 if the allocation is successful.
*/
int dchain_allocate(int index_range, struct DoubleChain** chain_out);
/*@ requires *chain_out |-> ?old_val &*&
             0 < index_range &*& index_range <= IRANG_LIMIT; @*/
/*@ ensures result == 0 ?
             *chain_out |-> old_val :
             (result == 1 &*& *chain_out |-> ?chp &*&
              double_chainp(empty_dchain_fp(index_range, 0), chp));
            @*/

/**
   Allocate a fresh index. If there is an unused, or expired index in the range,
   allocate it.

   @param chain - pointer to the allocator.
   @param index_out - output pointer to the newly allocated index.
   @param time - current time. Allocator will note this for the new index.
   @returns 0 if there is no space, and 1 if the allocation is successful.
 */
int dchain_allocate_new_index(struct DoubleChain* chain,
                              int* index_out, uint32_t time);
/*@ requires double_chainp(?ch, chain) &*&
             *index_out |-> ?i &*&
             dchain_high_fp(ch) <= time; @*/
/*@ ensures dchain_out_of_space_fp(ch) ?
            (result == 0 &*& *index_out |-> i &*&
             double_chainp(ch, chain)) :
            (result == 1 &*& *index_out |-> ?ni &*&
             false == dchain_allocated_fp(ch, ni) &*&
             0 <= ni &*& ni < dchain_index_range_fp(ch) &*&
             double_chainp(dchain_allocate_fp(ch, ni, time), chain)); @*/

/**
   Update the index timestamp. Needed to keep the index from expiration.

   @param chain - pointer to the allocator.
   @param index - the index to rejuvenate.
   @param time - the current time, it will replace the old timestamp.
   @returns 1 if the timestamp was updated, and 0 if the index is not tagged as
            allocated.
 */
int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time);
/*@ requires double_chainp(?ch, chain) &*&
             0 <= index &*& index < dchain_index_range_fp(ch) &*&
             dchain_high_fp(ch) <= time; @*/
/*@ ensures dchain_allocated_fp(ch, index) ?
            (dchain_get_time_fp(ch, index) <= time &*&
             result == 1 &*&
             double_chainp(dchain_rejuvenate_fp(ch, index, time), chain)) :
            (result == 0 &*&
             double_chainp(ch, chain)); @*/

/**
   Make space in the allocator by expiring the least recently used index.

   @param chain - pointer to the allocator.
   @param index_out - output pointer to the expired index.
   @param time - the time border, separating expired indexes from non-expired
                 ones.
   @returns 1 if the oldest index is older then current time and is expired,
   0 otherwise.
 */
int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time);
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

#endif //_DOUBLE_CHAIN_H_INCLUDED_
