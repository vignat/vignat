#ifndef _DOUBLE_CHAIN_H_INCLUDED_
#define _DOUBLE_CHAIN_H_INCLUDED_ 

int dchain_allocate(int index_range);
int dchain_allocate_new_index(int *index);
int dchain_free_index(int index);
int dchain_get_oldest_index(int *index);
int dchain_rejuvenate_index(int index);

#endif //_DOUBLE_CHAIN_H_INCLUDED_
