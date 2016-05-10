#ifndef _DOUBLE_CHAIN_H_INCLUDED_
#define _DOUBLE_CHAIN_H_INCLUDED_

#include <stdint.h>

struct DoubleChain;
/* Makes sure the allocator structur fits into memory, and particularly into
   32 bit address space. @*/
#define IRANG_LIMIT (1048576)

/*@
  inductive dchain = dchain(list<pair<int, uint32_t> >, int);

  predicate double_chainp(dchain ch,
                          struct DoubleChain* cp);

  fixpoint dchain empty_dchain_fp(int index_range) {
    return dchain(nil, index_range);
  }

  fixpoint bool dchain_out_of_space_fp(dchain ch) {
    switch(ch) { case dchain(alist, size):
      return size <= length(alist);
    }
  }

  fixpoint int dchain_index_range_fp(dchain ch) {
    switch(ch) { case dchain(alist, size): return size; }
  }

  fixpoint bool same_index(int i, pair<int, uint32_t> b) {
    return i == fst(b);
  }

  fixpoint bool dchain_allocated_fp(dchain ch, int index) {
    switch(ch) { case dchain(alist, size):
      return exists(alist, (same_index)(index));
    }
  }

  fixpoint dchain dchain_allocate_fp(dchain ch, int index, uint32_t t) {
    switch(ch) { case dchain(alist, size):
      return dchain(append(alist, cons(pair(index, t), nil)), size);
    }
  }

  fixpoint list<pair<int, uint32_t> >
    remove_by_index_fp(int i, list<pair<int, uint32_t> > lst) {
      switch(lst) {
        case nil: return nil;
        case cons(h,t):
          return fst(h) == i ? t :
                               cons(h, remove_by_index_fp(i, t));
      }
    }

  fixpoint dchain dchain_rejuvenate_fp(dchain ch, int index, uint32_t time) {
    switch(ch) { case dchain(alist, size):
      return dchain(append(remove_by_index_fp(index, alist),
                           cons(pair(index, time), nil)),
                    size);
    }
  }

  fixpoint bool dchain_is_empty_fp(dchain ch) {
    switch(ch) { case dchain(alist, size):
      return alist == nil;
    }
  }

  fixpoint int dchain_get_oldest_index_fp(dchain ch) {
    switch(ch) { case dchain(alist, size):
      return fst(head(alist));
    }
  }

  fixpoint uint32_t dchain_get_oldest_time_fp(dchain ch) {
    switch(ch) { case dchain(alist, size):
      return snd(head(alist));
    }
  }

  fixpoint dchain dchain_remove_index_fp(dchain ch, int index) {
    switch(ch) { case dchain(alist, size):
      return dchain(remove_by_index_fp(index, alist), size);
    }
  }

  fixpoint list<pair<int, uint32_t> >
    expire_old_indexes_fp(uint32_t time, list<pair<int, uint32_t> > lst) {
      switch(lst) {
        case nil: return nil;
        case cons(h,t):
          return snd(h) < time ?
                  expire_old_indexes_fp(time, t) :
                  lst;
      }
    }

  fixpoint dchain dchain_expire_old_indexes_fp(dchain ch, uint32_t time) {
    switch(ch) { case dchain(alist, size):
      return dchain(expire_old_indexes_fp(time, alist), size);
    }
  }

  fixpoint list<int>
  get_expired_indexes_fp(uint32_t time, list<pair<int, uint32_t> > lst) {
    switch(lst) {
      case nil: return nil;
      case cons(h,t):
        return snd(h) < time ?
                 cons(fst(h), get_expired_indexes_fp(time, t)) :
                 nil;
    }
  }

  fixpoint list<int> dchain_get_expired_indexes_fp(dchain ch, uint32_t time) {
    switch(ch) { case dchain(alist, size):
      return get_expired_indexes_fp(time, alist);
    }
  }

  lemma void expire_old_dchain_nonfull(dchain ch, uint32_t time);
  requires length(dchain_get_expired_indexes_fp(ch, time)) > 0;
  ensures dchain_out_of_space_fp(dchain_expire_old_indexes_fp(ch, time))
          == false;

  lemma void index_range_of_empty(int ir);
  requires 0 < ir;
  ensures dchain_index_range_fp(empty_dchain_fp(ir)) == ir;

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

  @*/

int dchain_allocate(int index_range, struct DoubleChain** chain_out);
/*@ requires *chain_out |-> ?old_val &*&
             0 < index_range &*& index_range <= IRANG_LIMIT; @*/
/*@ ensures result == 0 ?
             *chain_out |-> old_val :
             (result == 1 &*& *chain_out |-> ?chp &*&
              double_chainp(empty_dchain_fp(index_range), chp));
            @*/

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int* index_out, uint32_t time);
/*@ requires double_chainp(?ch, chain) &*& *index_out |-> ?i; @*/
/*@ ensures dchain_out_of_space_fp(ch) ?
            (result == 0 &*& *index_out |-> i &*&
             double_chainp(ch, chain)) :
            (result == 1 &*& *index_out |-> ?in &*&
             false == dchain_allocated_fp(ch, in) &*&
             0 <= in &*& in < dchain_index_range_fp(ch) &*&
             double_chainp(dchain_allocate_fp(ch, in, time), chain)); @*/

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time);
/*@ requires double_chainp(?ch, chain) &*&
             0 <= index &*& index < dchain_index_range_fp(ch); @*/
/*@ ensures dchain_allocated_fp(ch, index) ?
            (result == 1 &*&
             double_chainp(dchain_rejuvenate_fp(ch, index, time), chain)) :
            (result == 0 &*&
             double_chainp(ch, chain)); @*/

int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time);
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

#endif //_DOUBLE_CHAIN_H_INCLUDED_
