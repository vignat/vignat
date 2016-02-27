#ifndef _DOUBLE_CHAIN_H_INCLUDED_
#define _DOUBLE_CHAIN_H_INCLUDED_

#include <stdint.h>

struct DoubleChain;
/*@
  inductive dchain = dchain;

  predicate double_chainp(dchain ch, int index_range,
                          struct DoubleChain* cp) = true;

  fixpoint dchain empty_dchain_fp();

  fixpoint bool dchain_out_of_space_fp(dchain ch);

  fixpoint int dchain_get_next_index_fp(dchain ch);
  fixpoint dchain dchain_take_next_index_fp(dchain ch);

  fixpoint dchain dchain_rejuvenate_fp(dchain ch, int index, uint32_t time);
  fixpoint bool dchain_allocated_index_fp(dchain ch, int index);

  fixpoint bool dchain_is_empty_fp(dchain ch);
  fixpoint int dchain_get_oldest_index_fp(dchain ch);
  fixpoint uint32_t dchain_get_oldest_time_fp(dchain ch);
  fixpoint dchain dchain_remove_index_fp(dchain ch, int index);

  fixpoint dchain dchain_expire_old_indexes_fp(dchain ch, uint32_t time);
  fixpoint list<int> dchain_get_expired_indexes_fp(dchain ch, uint32_t time);

  lemma void dchain_next_index_not_allocated(dchain ch);
  requires true;
  ensures false == dchain_allocated_index_fp(ch, dchain_get_next_index_fp(ch));
  @*/

int dchain_allocate(int index_range, struct DoubleChain** chain_out);
/*@ requires pointer(chain_out, _); @*/
/*@ ensures result == 0 ? true :
            (result == 1 &*& *chain_out |-> ?chp &*&
             double_chainp(empty_dchain_fp(), index_range, chp));
            @*/

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int* index_out, uint32_t time);
/*@ requires double_chainp(?ch, ?index_range, chain) &*& *index_out |-> ?i; @*/
/*@ ensures dchain_out_of_space_fp(ch) ?
            (result == 0 &*& *index_out |-> i &*&
             double_chainp(ch, index_range, chain)) :
            (result == 1 &*& *index_out |-> ?io &*&
             io == dchain_get_next_index_fp(ch) &*&
             0 <= io &*& io < index_range &*&
             double_chainp(dchain_take_next_index_fp(ch), index_range, chain)); @*/

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time);
/*@ requires double_chainp(?ch, ?index_range, chain) &*&
             0 <= index &*& index < index_range; @*/
/*@ ensures dchain_allocated_index_fp(ch, index) ?
            (result == 1 &*&
             double_chainp(dchain_rejuvenate_fp(ch, index, time), index_range, chain)) :
            (result == 0 &*&
             double_chainp(ch, index, chain)); @*/
int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time);
//^^^ Never call this funciton in this application -  no contract here.

#endif //_DOUBLE_CHAIN_H_INCLUDED_
