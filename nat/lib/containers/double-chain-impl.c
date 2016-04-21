#include "double-chain-impl.h"

enum DCHAIN_ENUM {
    ALLOC_LIST_HEAD = 0,
    FREE_LIST_HEAD = 1,
    INDEX_SHIFT = DCHAIN_RESERVED
};

/*@

  inductive fcell = fcell(int, int);
  inductive bcell = bcell(int, int, int);

  fixpoint int get_bcell_ind(bcell bc) {
    switch(bc) { case bcell(ind,prev,next): return ind; }
  }

  fixpoint list<fcell> free_list_fp(list<dcell> arr, int start_index) {
    switch(arr) {
      case nil: return nil;
      case cons(h,t):
        return (dchain_cell_get_prev(h) == dchain_cell_get_next(h) ?
                cons(fcell(start_index, dchain_cell_get_next(h)),
                     free_list_fp(t, start_index+1)) :
                free_list_fp(t, start_index+1));
    }
  }

  fixpoint list<bcell> busy_list_fp(list<dcell> arr, int start_index) {
    switch(arr) {
      case nil: return nil;
      case cons(h,t):
        return (dchain_cell_get_prev(h) != dchain_cell_get_next(h) ?
                cons(bcell(start_index, dchain_cell_get_prev(h),
                           dchain_cell_get_next(h)),
                     busy_list_fp(t, start_index+1)) :
                busy_list_fp(t, start_index+1));
    }
  }

  fixpoint list<int> get_indexes_fp(list<bcell> bls) {
    switch(bls) {
      case nil: return nil;
      case cons(h,t):
        return cons(get_bcell_ind(h), get_indexes_fp(t));
    }
  }

  predicate dchainip(dchaini ch,
                     struct dchain_cell * cells) =
    switch(ch) { case dchaini(allocd, size):
      return
        INDEX_SHIFT < size &*&
        dcellsp(cells, size, ?cls) &*&
        allocd == get_indexes_fp(busy_list_fp(cls,0));
    };
  @*/

void dchain_impl_init(struct dchain_cell *cells, int size)
/*@ requires 0 < size &*&
             dcellsp(cells, size + DCHAIN_RESERVED, _); @*/
/*@ ensures dchainip(empty_dchaini_fp(size), cells); @*/
{
  struct dchain_cell* al_head = cells + ALLOC_LIST_HEAD;
  al_head->prev = 0;
  al_head->next = 0;
  int i = INDEX_SHIFT;
  //@ open dcellsp(cells, size + 2, _);
  //@ open dcellsp(cells+1, size + 1, _);
  struct dchain_cell* fl_head = cells + FREE_LIST_HEAD;
  fl_head->next = i;
  fl_head->prev = fl_head->next;
  cells[FREE_LIST_HEAD].next = i;
  cells[FREE_LIST_HEAD].prev = cells[FREE_LIST_HEAD].next;
  while (i < (size + INDEX_SHIFT - 1)) {
    cells[i].next = i+1;
    cells[i].prev = cells[i].next;
    ++i;
  }
  cells[i].next = FREE_LIST_HEAD;
  cells[i].prev = cells[i].next;
}

int dchain_impl_allocate_new_index(struct dchain_cell *cells, int *index)
/*@ requires dchainip(?dc, cells) &*& *index |-> ?i; @*/
/*@ ensures (dchaini_out_of_space_fp(dc) ?
             (result == 0 &*&
              dchainip(dc, cells) &*& *index |-> i &*& result == 0) :
             (result == 1 &*&
              *index |-> ?ni &*&
              false == dchaini_allocated_fp(dc, ni) &*&
              dchainip(dchaini_allocate_fp(dc, ni), cells))); @*/
{
    /* No more empty cells. */
    if (cells[FREE_LIST_HEAD].next == FREE_LIST_HEAD)
        return 0;
    int allocated = cells[FREE_LIST_HEAD].next;
    /* Extract the link from the "empty" chain. */
    cells[FREE_LIST_HEAD].next = cells[allocated].next;
    
    /* Add the link to the "new"-end "alloc" chain. */
    cells[allocated].next = ALLOC_LIST_HEAD;
    cells[allocated].prev = cells[ALLOC_LIST_HEAD].prev;
    cells[cells[ALLOC_LIST_HEAD].prev].next = allocated;
    cells[ALLOC_LIST_HEAD].prev = allocated;

    *index = allocated - INDEX_SHIFT;
    return 1;
}

int dchain_impl_free_index(struct dchain_cell *cells, int index)
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_fp(dc, index) ?
             (dchainip(dchaini_remove_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/
{
    int freed = index + INDEX_SHIFT;
    /* The index is already free. */
    if (cells[freed].next == cells[freed].prev)
        return 0;
    /* Extract the link from the "alloc" chain. */
    cells[cells[freed].prev].next = cells[freed].next;
    cells[cells[freed].next].prev = cells[freed].prev;

    /* Add the link to the "free" chain. */
    cells[freed].next = cells[FREE_LIST_HEAD].next;
    cells[freed].prev = cells[freed].next;
    cells[FREE_LIST_HEAD].next = freed;
    cells[FREE_LIST_HEAD].prev = cells[FREE_LIST_HEAD].next;
    return 1;
}

int dchain_impl_get_oldest_index(struct dchain_cell *cells, int *index)
/*@ requires dchainip(?dc, cells) &*& *index |-> ?i; @*/
/*@ ensures dchainip(dc, cells) &*&
            (dchaini_is_empty_fp(dc) ?
             (*index |-> i &*&
              result == 0) :
             (*index |-> dchaini_get_oldest_index_fp(dc) &*&
              result == 1)); @*/
{
    /* No allocated indexes. */
    if (cells[ALLOC_LIST_HEAD].next == cells[ALLOC_LIST_HEAD].prev)
        return 0;
    *index = cells[ALLOC_LIST_HEAD].next - INDEX_SHIFT;
    return 1;
}

int dchain_impl_rejuvenate_index(struct dchain_cell *cells, int index)
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_fp(dc, index) ?
             (dchainip(dchaini_rejuvenate_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/
{
    int lifted = index + INDEX_SHIFT;
    /* The index is not allocated. */
    if (cells[lifted].next == cells[lifted].prev)
        return 0;
    
    /* Unlink it from the middle of the "alloc" chain. */
    cells[cells[lifted].prev].next = cells[lifted].next;
    cells[cells[lifted].next].prev = cells[lifted].prev;

    /* Link it at the very end - right before the special link. */
    cells[lifted].next = ALLOC_LIST_HEAD;
    cells[lifted].prev = cells[ALLOC_LIST_HEAD].prev;
    cells[cells[ALLOC_LIST_HEAD].prev].next = lifted;
    cells[ALLOC_LIST_HEAD].prev = lifted;
    return 1;
}

