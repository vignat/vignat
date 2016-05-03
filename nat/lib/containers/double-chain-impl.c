#include "double-chain-impl.h"

//@ #include <nat.gh>
//@ #include "arith.gh"

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
        dcellsp(cells, size + INDEX_SHIFT, ?cls) &*&
        allocd == get_indexes_fp(busy_list_fp(cls,0));
    };

  lemma void dcell_limits(struct dchain_cell* p)
  requires [?f]dcellp(p, ?v);
  ensures [f]dcellp(p, v) &*& p > (struct dchain_cell *)0 &*&
                              p + 1 <= (struct dchain_cell *)UINTPTR_MAX;
  {
    assume(sizeof(struct dchain_cell) == sizeof(int) + sizeof(int));
    assume((void*)&p->prev + sizeof(int) <= (void*)&p->next);
    open [f]dcellp(p,v);
    open [f]dchain_cell_prev(p,?prev);
    open [f]dchain_cell_next(p,?next);
    integer_limits((void*)&p->prev);
    integer_limits((void*)&p->next);
    integer_to_chars((void*)&p->prev);
    integer_to_chars((void*)&p->next);

    chars_limits((void*)p);

    chars_to_integer((void*)&p->next);
    chars_to_integer((void*)&p->prev);
    int_of_chars_of_int(prev);
    int_of_chars_of_int(next);

    close [f]dchain_cell_next(p,next);
    close [f]dchain_cell_prev(p,prev);
    close [f]dcellp(p,v);
  }

  lemma void dcells_limits(struct dchain_cell* p)
  requires [?f]dcellsp(p, ?len, ?val) &*& 0 < len;
  ensures [f]dcellsp(p, len, val) &*&
          p > (struct dchain_cell *)0 &*&
          p + len <= (struct dchain_cell *)UINTPTR_MAX;
  {
    open [f]dcellsp(p, len, val);
    switch(val) {
      case nil: break;
      case cons(h,t):
        dcell_limits(p);
        if (1 < len) dcells_limits(p+1);
    }
    close [f]dcellsp(p, len, val);
  }

  fixpoint list<dcell> empty_cells_seg(nat len, int ind) {
    switch(len) {
    case zero:
        return nil;
      case succ(n):
        return cons(dcell(ind+1, ind+1), empty_cells_seg(n, ind+1));
    }
  }

  lemma void initial_empty_cell(int ind)
  requires true;
  ensures empty_cells_seg(nat_of_int(1), ind) == cons(dcell(ind+1,ind+1),nil);
  {
    assert(nat_of_int(1) == succ(zero));
    assert(empty_cells_seg(zero, ind+1) == nil);
    assert(empty_cells_seg(succ(zero), ind) ==
           cons(dcell(ind+1,ind+1), empty_cells_seg(zero, ind+1)));
  }

  lemma void put_cell_back_ind(struct dchain_cell* cells, nat len, int start_ind)
  requires dcellsp(cells, int_of_nat(len), empty_cells_seg(len, start_ind)) &*&
           dcellp(cells+int_of_nat(len),
                  dcell(int_of_nat(len)+start_ind+1,
                        int_of_nat(len)+start_ind+1));
  ensures dcellsp(cells, int_of_nat(len) + 1, empty_cells_seg(succ(len), start_ind));
  {
    switch(len) {
      case zero:
      case succ(n):
        mul_subst(1+int_of_nat(n), int_of_nat(len), sizeof(struct dchain_cell));
        put_cell_back_ind(cells+1, n, start_ind+1);
    }
  }

  lemma void put_cell_back(struct dchain_cell* cells, int len, int start_ind)
  requires dcellsp(cells, len, empty_cells_seg(nat_of_int(len), start_ind)) &*&
           dcellp(cells+len, dcell(len+start_ind+1,len+start_ind+1)) &*&
           0 <= len;
  ensures dcellsp(cells, len + 1, empty_cells_seg(nat_of_int(len+1), start_ind));
  {
    put_cell_back_ind(cells, nat_of_int(len), start_ind);
  }

  lemma void empty_dchain_produced_tail(struct dchain_cell* cells, nat len, int ind)
  requires dcellsp(cells, int_of_nat(len), empty_cells_seg(len, ind)) &*&
           dcellp(cells + int_of_nat(len), dcell(1,1));
  ensures dcellsp(cells, int_of_nat(len)+1, ?lst) &*& busy_list_fp(lst,ind) == nil;
  {
    switch(len) {
      case zero:
        return;
      case succ(n):
        open dcellsp(cells, int_of_nat(len), empty_cells_seg(len, ind));
        assert dcellp(cells, dcell(ind+1,ind+1));
        assert 1+int_of_nat(n) == int_of_nat(len);
        mul_subst(1+int_of_nat(n), int_of_nat(len), sizeof(struct dchain_cell));
        empty_dchain_produced_tail(cells+1, n, ind+1);
        assert dcellsp(cells+1, int_of_nat(n)+1, ?lst);
        close dcellsp(cells, int_of_nat(len)+1, cons(dcell(ind+1,ind+1), lst));
    }
  }

  lemma void empty_dchain_produced(struct dchain_cell* cells, int len)
  requires dcellp(cells, dcell(0,0)) &*& dcellsp(cells+1, len,
                                                 empty_cells_seg(nat_of_int(len), 1)) &*&
           dcellp(cells + len + 1, dcell(1,1)) &*&
           0 < len;
  ensures dcellsp(cells, len+2, ?lst) &*& busy_list_fp(lst,0) == nil;
  {
    empty_dchain_produced_tail(cells+1, nat_of_int(len), 1);
    assert dcellsp(cells+1, len+1, ?lst);
    close dcellsp(cells, len+2, cons(dcell(0,0), lst));
  }
  @*/

void dchain_impl_init(struct dchain_cell *cells, int size)
/*@ requires 0 < size &*&
             size < INT_MAX - 2 &*&
             dcellsp(cells, size + DCHAIN_RESERVED, _); @*/
/*@ ensures dchainip(empty_dchaini_fp(size), cells); @*/
{
  //@ open dcellsp(cells, size + 2, _);
  //@ dcell_limits(cells);
  struct dchain_cell* al_head = cells + ALLOC_LIST_HEAD;
  al_head->prev = 0;
  al_head->next = 0;
  int i = INDEX_SHIFT;
  //@ open dcellsp(cells + 1, size + 1, _);
  //@ dcell_limits(cells + 1);
  struct dchain_cell* fl_head = cells + FREE_LIST_HEAD;
  fl_head->next = i;
  fl_head->prev = fl_head->next;
  //@ initial_empty_cell(FREE_LIST_HEAD);
  while (i < (size + INDEX_SHIFT - 1))
    /*@ invariant INDEX_SHIFT <= i &*&
                  i <= size + INDEX_SHIFT -1 &*&
                  cells > (struct dchain_cell*)0 &*&
                  dcellsp(cells + i, size + DCHAIN_RESERVED - i, _) &*&
                  dcellsp(cells + FREE_LIST_HEAD, i - FREE_LIST_HEAD,
                          empty_cells_seg(nat_of_int(i - FREE_LIST_HEAD),
                                          FREE_LIST_HEAD));
                  @*/
  {
    //@ open dcellsp(cells + i, size + DCHAIN_RESERVED - i, _);
    //@ dcell_limits(cells + i);
    struct dchain_cell* current = cells + i;
    current->next = i+1;
    current->prev = current->next;
    //@ put_cell_back(cells + FREE_LIST_HEAD, i - FREE_LIST_HEAD, FREE_LIST_HEAD);
    ++i;
  }
  //@ assert i == size + INDEX_SHIFT - 1;
  //@ open dcellsp(cells + i, size + DCHAIN_RESERVED - i, _);
  //@ dcell_limits(cells + i);
  struct dchain_cell* last = cells + i;
  last->next = FREE_LIST_HEAD;
  last->prev = last->next;
  //@ assert i == size + 1;
  //@ mul_subst(i, size+1, sizeof(struct dchain_cell));
  //@ close dcellp(cells+size+1,dcell(1,1));
  //@ empty_dchain_produced(cells, size);
  //@ close dchainip(empty_dchaini_fp(size), cells);
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

