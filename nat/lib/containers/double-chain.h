#ifndef _DOUBLE_CHAIN_H_INCLUDED_
#define _DOUBLE_CHAIN_H_INCLUDED_ 

//@ #include "lib/predicates.gh"

int dchain_allocate(int index_range);
/*@ requires true; @*/
/*@ ensures result == 0 ? true :
            (result == 1 &*&
             double_chain_p(?chain, index_range));
            @*/

int dchain_allocate_new_index(int *index);
/*@ requires double_chain_p(?chain, ?index_range) &*& *index |-> ?i; @*/
/*@ ensures double_chain_p(chain, index_range) &*&
            result == 0 ? *index |-> i :
                          (*index |-> ?j &*& 0 <= j &*& j <= index_range &*&
                           dchain_is_allocated(chain, j) == true); @*/
int dchain_free_index(int index);
int dchain_get_oldest_index(int *index);
int dchain_rejuvenate_index(int index);
/*@ requires double_chain_p(?chain, ?index_range) &*&
             0 <= index &*& index < index_range; @*/
/*@ ensures double_chain_p(chain, index_range) &*&
            dchain_is_allocated(chain, index) ? result == 1 : result == 0; @*/

#endif //_DOUBLE_CHAIN_H_INCLUDED_
