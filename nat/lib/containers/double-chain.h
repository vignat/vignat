#ifndef _DOUBLE_CHAIN_H_INCLUDED_
#define _DOUBLE_CHAIN_H_INCLUDED_ 

//@ #include "lib/predicates.gh"

int dchain_allocate(int index_range);
//@ requires true;
//@ ensures result == 0 ? true : result == 1 &*& \
            double_chain_p(?chain, index_range);

int dchain_allocate_new_index(int *index);
int dchain_free_index(int index);
int dchain_get_oldest_index(int *index);
int dchain_rejuvenate_index(int index);

#endif //_DOUBLE_CHAIN_H_INCLUDED_
