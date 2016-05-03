#include "double-chain-impl.h"

//@ #include <nat.gh>
//@ #include <listex.gh>
//@ #include "arith.gh"

enum DCHAIN_ENUM {
    ALLOC_LIST_HEAD = 0,
    FREE_LIST_HEAD = 1,
    INDEX_SHIFT = DCHAIN_RESERVED
};

/*@

  predicate free_listp(list<dcell> cells, list<int> fl, int cur) =
    switch(fl) {
      case nil: return ALLOC_LIST_HEAD < cur &*&
                       nth(cur, cells) == dcell(1,1);
      case cons(h,t):
        return nth(cur, cells) == dcell(h,h) &*&
               ALLOC_LIST_HEAD < cur &*&
               free_listp(cells, t, h);
    };

  predicate alloc_listp(list<dcell> cells, list<int> alloc, int cur) =
    switch(alloc) {
      case nil: return nth(cur, cells) == dcell(?x,0) &*&
                       cur == 0 ? x == 0 : true;
      case cons(h,t):
        return nth(cur, cells) == dcell(?x, h) &*&
               nth(h, cells) == dcell(cur, ?y) &*&
               x != h &*& y != cur &*&
               alloc_listp(cells, t, h);
    };

  fixpoint list<int> shift_inds_fp(list<int> inds, int shift) {
    switch(inds) {
      case nil: return nil;
      case cons(h,t): return cons(h+shift, shift_inds_fp(t, shift));
    }
  }

  fixpoint bool bounded(int bound, dcell val) {
    return 0 <= dchain_cell_get_prev(val) &&
                dchain_cell_get_prev(val) < bound &&
           0 <= dchain_cell_get_next(val) &&
                dchain_cell_get_next(val) < bound;
  }

  predicate dchainip(dchaini ch,
                     struct dchain_cell * cells) =
    switch(ch) { case dchaini(allocd, size):
      return
        0 < size &*&
        dcellsp(cells, size + INDEX_SHIFT, ?cls) &*&
        true == forall(cls, (bounded)(size+INDEX_SHIFT)) &*&
        alloc_listp(cls, ?al, 0) &*&
        free_listp(cls, ?fl, 1) &*&
        length(al) + length(fl) == size &*&
        al == shift_inds_fp(allocd, INDEX_SHIFT);
    };
    @*/

/*@
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
  @*/

/*@
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

  @*/

/*@

  fixpoint list<int> full_free_list_fp(nat len, int cur) {
    switch(len) {
      case zero: return nil;
      case succ(n): return cons(cur,full_free_list_fp(n,cur+1));
    }
  }

  lemma void full_free_list_len(nat len, int cur)
  requires true;
  ensures length(full_free_list_fp(len, cur)) == int_of_nat(len);
  {
    switch(len) {
      case zero: return;
      case succ(n): full_free_list_len(n, cur+1);
    }
  }

  lemma void append_append_cons_to_append_cons<t>(list<t> l1, t el, list<t> l2)
  requires true;
  ensures append(append(l1, cons(el, nil)), l2) == append(l1, cons(el, l2));
  {
    switch(l1) {
      case nil: return;
      case cons(h,t):
        append_append_cons_to_append_cons(t, el, l2);
    }
  }

  lemma void empty_dchain_produced_tail(struct dchain_cell* cells,
                                        nat len,
                                        int ind,
                                        int size,
                                        list<dcell> pref)
  requires dcellsp(cells + ind, int_of_nat(len), empty_cells_seg(len, ind)) &*&
           dcellp(cells + ind + int_of_nat(len), dcell(1,1)) &*&
           length(pref) == ind &*&
           ind + int_of_nat(len) < size &*&
           1 < size &*&
           0 < ind &*&
           true == forall(pref, (bounded)(size));
  ensures dcellsp(cells + ind, int_of_nat(len)+1, ?lst) &*&
          free_listp(append(pref, lst), full_free_list_fp(len, ind+1), ind) &*&
          true == forall(append(pref, lst), (bounded)(size));
  {
    switch(len) {
      case zero:
        close dcellsp(cells + ind, 1, cons(dcell(1,1), nil));
        nth_append_r(pref, cons(dcell(1,1), nil), 0);
        forall_append(pref, cons(dcell(1,1), nil), (bounded)(size));
        close free_listp(append(pref, cons(dcell(1,1), nil)), nil, ind);
        return;
      case succ(n):
        open dcellsp(cells + ind, int_of_nat(len), empty_cells_seg(len, ind));
        assert dcellp(cells + ind, dcell(ind+1,ind+1));
        assert ind+1+int_of_nat(n) == ind+int_of_nat(len);
        mul_subst(ind+1+int_of_nat(n), ind+int_of_nat(len), sizeof(struct dchain_cell));
        forall_append(pref, cons(dcell(ind+1,ind+1), nil), (bounded)(size));
        empty_dchain_produced_tail(cells, n, ind+1, size,
                                   append(pref,cons(dcell(ind+1,ind+1), nil)));
        assert dcellsp(cells+ind+1, int_of_nat(n)+1, ?lst_tail);
        assert free_listp(append(append(pref, cons(dcell(ind+1,ind+1),
                                              nil)), lst_tail),
                          full_free_list_fp(n, ind+2), ind+1);
        close dcellsp(cells+ind, int_of_nat(len)+1,
                      cons(dcell(ind+1,ind+1), lst_tail));

        nth_append_r(pref, cons(dcell(ind+1,ind+1), lst_tail), 0);
        append_append_cons_to_append_cons(pref, dcell(ind+1,ind+1), lst_tail);
        close free_listp(append(pref, cons(dcell(ind+1,ind+1), lst_tail)),
                         full_free_list_fp(len, ind+1), ind);
    }
  }

  lemma void empty_dchain_produced(struct dchain_cell* cells, int len)
  requires dcellp(cells, dcell(0,0)) &*& dcellsp(cells+1, len,
                                                 empty_cells_seg(nat_of_int(len), 1)) &*&
           dcellp(cells + len + 1, dcell(1,1)) &*&
           0 < len;
  ensures dcellsp(cells, len+2, ?lst) &*&
          true == forall(lst, (bounded)(len+2)) &*&
          free_listp(lst, full_free_list_fp(nat_of_int(len), 2), 1) &*&
          alloc_listp(lst, nil, 0);
  {
    empty_dchain_produced_tail(cells, nat_of_int(len), 1, len+2,
                               cons(dcell(0,0),nil));
    assert dcellsp(cells+1, len+1, ?lst);
    close dcellsp(cells, len+2, cons(dcell(0,0), lst));
    close alloc_listp(cons(dcell(0,0), lst), nil, 0);
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
  //@ full_free_list_len(nat_of_int(size), 2);
  //@ close dchainip(empty_dchaini_fp(size), cells);
}

/*@
  lemma void short_circuited_free_list(list<dcell> cells, list<int> fl);
  requires free_listp(cells, fl, 1) &*&
           dchain_cell_get_next(nth(1, cells)) == 1;
  ensures free_listp(cells, fl, 1) &*& fl == nil;

  fixpoint list<int> dchaini_alist_fp(dchaini dc) {
    switch(dc) { case dchaini(alist, size): return alist; }
  }

  lemma void shift_inds_len(list<int> l, int shift)
  requires true;
  ensures length(shift_inds_fp(l, shift)) == length(l);
  {
    switch(l) {
      case nil: return;
      case cons(h,t): shift_inds_len(t, shift);
    }
  }
  @*/

/*@
  lemma void extract_cell(struct dchain_cell* cells, list<dcell> cls, int i)
  requires dcellsp(cells, ?size, cls) &*&
           0 <= i &*& i < size;
  ensures dcellsp(cells, i, take(i, cls)) &*& dcellp(cells+i, nth(i, cls)) &*&
          dcellsp(cells+i+1, size - i - 1, drop(i+1, cls));
  {
    open dcellsp(cells, size, cls);
    switch(cls) {
      case nil:
        assert(size == 0);
        assert(0 <= i);
        assert(i < 0);
        return;
      case cons(h,t):
        if (i == 0) {
        } else {
          extract_cell(cells+1, t, i-1);
        }
    }
    close dcellsp(cells, i, take(i, cls));
  }

  lemma void glue_cells(struct dchain_cell* cells, list<dcell> cls, int i)
  requires 0 <= i &*& i < length(cls) &*&
           dcellsp(cells, i, take(i, cls)) &*& dcellp(cells+i, nth(i, cls)) &*&
           dcellsp(cells+i+1, length(cls) - i - 1, drop(i+1, cls));
  ensures dcellsp(cells, length(cls), cls);
  {
    switch(cls) {
      case nil:
        assert(0 <= i);
        assert(i < 0);
        return;
      case cons(h,t):
        open dcellsp(cells, i, take(i, cls));
        if (i == 0) {
        } else {
          glue_cells(cells+1, t, i-1);
        }
        close dcellsp(cells, length(cls), cls);
    }
  }

  lemma void dcellsp_length(struct dchain_cell* cells)
  requires dcellsp(cells, ?size, ?cls);
  ensures dcellsp(cells, size, cls) &*& size == length(cls);
  {
    open dcellsp(cells, size, cls);
    switch(cls) {
      case nil: return;
      case cons(h,t): dcellsp_length(cells+1);
    }
    close dcellsp(cells, size, cls);
  }

  lemma void forall_nth<t>(list<t> lst, fixpoint(t, bool) p, int i)
  requires 0 <= i &*& i < length(lst) &*& true == forall(lst, p);
  ensures true == p(nth(i, lst));
  {
    switch(lst) {
      case nil: return;
      case cons(h,t):
        if (i == 0){}
        else {
          forall_nth(t, p, i-1);
        }
    }
  }

  lemma void free_list_above_alloc(list<dcell> cls, list<int> fl, int ind)
  requires free_listp(cls, fl, ind);
  ensures free_listp(cls, fl, ind) &*&
          ALLOC_LIST_HEAD < dchain_cell_get_next(nth(ind, cls));
  {
    open free_listp(cls, fl, ind);
    switch(fl) {
      case nil: break;
      case cons(h,t):
        open free_listp(cls, t, h);
        close free_listp(cls, t, h);
     };
     close free_listp(cls, fl, ind);
  }
  @*/


int dchain_impl_allocate_new_index(struct dchain_cell *cells, int *index)
/*@ requires dchainip(?dc, cells) &*& *index |-> ?i; @*/
/*@ ensures (dchaini_out_of_space_fp(dc) ?
             (result == 0 &*&
              dchainip(dc, cells) &*&
              *index |-> i) :
             (result == 1 &*&
              *index |-> ?ni &*&
              false == dchaini_allocated_fp(dc, ni) &*&
              dchainip(dchaini_allocate_fp(dc, ni), cells))); @*/
{
  //@ open dchainip(dc, cells);
  //@ dcells_limits(cells);
  //@ int size = dchaini_irange_fp(dc);
  //@ assert 0 < size;
  //@ assert dcellsp(cells, size + INDEX_SHIFT, ?cls);
  //@ dcellsp_length(cells);
  //@ assert free_listp(cls, ?fl, 1);
  //@ assert alloc_listp(cls, ?al, 0);
  /* No more empty cells. */
  //@ mul_nonnegative(size, sizeof(struct dchain_cell));
  // @ open dcellsp(cells, size+INDEX_SHIFT, _);
  // @ open dcellsp(cells+1, size+INDEX_SHIFT-1, _);
  //@ extract_cell(cells, cls, FREE_LIST_HEAD);
  struct dchain_cell* fl_head = cells + FREE_LIST_HEAD;
  struct dchain_cell* al_head = cells + ALLOC_LIST_HEAD;
  if (fl_head->next == FREE_LIST_HEAD)
  {
    //@ glue_cells(cells, cls, FREE_LIST_HEAD);
    //@ short_circuited_free_list(cls, fl);
    // @ close dcellsp(cells+1, size+INDEX_SHIFT-1, _);
    // @ close dcellsp(cells, size+INDEX_SHIFT, _);
    //@ assert(length(al) == size);
    //@ shift_inds_len(dchaini_alist_fp(dc), INDEX_SHIFT);
    //@ assert(length(dchaini_alist_fp(dc)) == size);
    //@ close dchainip(dc, cells);
    //@ assert true == dchaini_out_of_space_fp(dc);
    return 0;
  }
  int allocated = fl_head->next;
  //@ forall_nth(cls, (bounded)(size+INDEX_SHIFT), FREE_LIST_HEAD);
  //@ assert 0 <= allocated &*& allocated < size + 2;
  //@ assert FREE_LIST_HEAD != allocated;
  //@ free_list_above_alloc(cls, fl, 1);
  //@ mul_bounds(allocated, size+2, sizeof(struct dchain_cell), sizeof(struct dchain_cell));
  //@ glue_cells(cells, cls, FREE_LIST_HEAD);
  //@ extract_cell(cells, cls, FREE_LIST_HEAD);
  //@ extract_cell(cells+INDEX_SHIFT, drop(INDEX_SHIFT,cls), allocated);
  struct dchain_cell* allocp = cells + allocated;
  /* Extract the link from the "empty" chain. */
  fl_head->next = allocp->next;

  /* Add the link to the "new"-end "alloc" chain. */
  allocp->next = ALLOC_LIST_HEAD;
  allocp->prev = al_head->prev;
  //@ glue_cells(cells, take(allocated, cls), FREE_LIST_HEAD);
  //@ glue_cells(cells, cls, allocated);
  //@ extract_cell(cells, cls, FREE_LIST_HEAD);
  struct dchain_cell* alloc_head_prevp = cells + al_head->prev;
  alloc_head_prevp->next = allocated;
  al_head->prev = allocated;

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

