#include "double-chain-impl.h"

//@ #include <nat.gh>
//@ #include <listex.gh>
//@ #include "arith.gh"
//@ #include "stdex.gh"

enum DCHAIN_ENUM {
    ALLOC_LIST_HEAD = 0,
    FREE_LIST_HEAD = 1,
    INDEX_SHIFT = DCHAIN_RESERVED
};

/*@

  predicate free_listp(list<dcell> cells, list<int> fl, int start, int cur) =
    switch(fl) {
      case nil: return nth(cur, cells) == dcell(start, start);
      case cons(h,t):
        return nth(cur, cells) == dcell(h, h) &*&
               cur != h &*&
               free_listp(cells, t, start, h);
    };

  predicate alloc_listp(list<dcell> cells, list<int> al, int start, int cur) =
    switch(al) {
      case nil: return nth(cur, cells) == dcell(?x, start) &*&
                       nth(start, cells) == dcell(cur, ?y) &*&
                       cur == start ?
                         (x == start &*& y == cur) :
                         true;
      case cons(h,t):
        return nth(cur, cells) == dcell(?x, h) &*&
               nth(h, cells) == dcell(cur, ?y) &*&
               cur != h &*&
               alloc_listp(cells, t, start, h);
    };

  fixpoint list<int> shift_inds_fp(list<int> inds, int shift) {
    switch(inds) {
      case nil: return nil;
      case cons(h,t): return cons(h+shift, shift_inds_fp(t, shift));
    }
  }

  fixpoint bool dbounded(int dbound, dcell val) {
    return 0 <= dchain_cell_get_prev(val) &&
                dchain_cell_get_prev(val) < dbound &&
           0 <= dchain_cell_get_next(val) &&
                dchain_cell_get_next(val) < dbound;
  }

  fixpoint bool lbounded(int lb, int x) {
    return lb <= x;
  }

  fixpoint bool all_engaged(list<int> al, list<int> fl, nat size) {
    switch(size) {
      case zero: return true;
      case succ(n):
        return all_engaged(al, fl, n) &&
              ( mem(int_of_nat(n) + INDEX_SHIFT, al) ?
               !mem(int_of_nat(n) + INDEX_SHIFT, fl) :
                mem(int_of_nat(n) + INDEX_SHIFT, fl) );
    }
  }

  predicate dchainip(dchaini ch,
                     struct dchain_cell * cells) =
    switch(ch) { case dchaini(allocd, size):
      return
        0 < size &*&
        size + INDEX_SHIFT < INT_MAX &*&
        dcellsp(cells, size + INDEX_SHIFT, ?cls) &*&
        true == forall(cls, (dbounded)(size+INDEX_SHIFT)) &*&
        alloc_listp(cls, ?al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD) &*&
        free_listp(cls, ?fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*&
        true == all_engaged(al, fl, nat_of_int(size)) &*&
        length(al) + length(fl) == size &*&
        true == forall(al, (lbounded)(INDEX_SHIFT)) &*&
        true == forall(fl, (lbounded)(INDEX_SHIFT)) &*&
        al == shift_inds_fp(allocd, INDEX_SHIFT);
    };
    @*/

/*@
  lemma void dcell_limits(struct dchain_cell* p)
  requires [?f]dcellp(p, ?v);
  ensures [f]dcellp(p, v) &*& p > (struct dchain_cell *)0 &*&
                              p + 1 <= (struct dchain_cell *)UINTPTR_MAX;
  {
    dcell_layout_assumptions(p);
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

  fixpoint bool some_engaged(list<int> lst, nat from, nat to) {
    switch(to) {
      case zero: return true;
      case succ(n):
        return mem(int_of_nat(n) + INDEX_SHIFT, lst) &&
                  (from == n ? true : some_engaged(lst, from, n));
    }
  }

  lemma void some_engaged_over_bigger_list(nat len, nat from, nat to, int i)
  requires true == some_engaged(full_free_list_fp(len, i+1), from, to);
  ensures true == some_engaged(full_free_list_fp(succ(len), i), from, to);
  {
    switch(to) {
      case zero: return;
      case succ(n):
        if (from != n)
          some_engaged_over_bigger_list(len, from, n, i);
    }
  }

  lemma void consolidate_some_engaged(list<int> lst, nat from, nat to)
  requires true == mem(int_of_nat(from) + INDEX_SHIFT, lst) &*&
           true == some_engaged(lst, succ(from), to);
  ensures true == some_engaged(lst, from, to);
  {
    switch(to) {
      case zero: return;
      case succ(n):
        if (n == succ(from)) {
          assert true == some_engaged(lst, from, to);
          return;
        }
        consolidate_some_engaged(lst, from, n);
    }
  }

  lemma void full_free_list_some_engaged(nat len, nat from, nat to, int i)
  requires int_of_nat(from) < int_of_nat(to) &*&
           int_of_nat(to) - int_of_nat(from) <= int_of_nat(len) &*&
           int_of_nat(from) + INDEX_SHIFT == i;
  ensures true == some_engaged(full_free_list_fp(len, i), from, to);
  {
    switch(len) {
      case zero: return;
      case succ(n):
        if (succ(from) == to) break;
        else {
          if (int_of_nat(succ(from)) == int_of_nat(to)) {
            assert(nat_of_int(int_of_nat(succ(from))) ==
                   nat_of_int(int_of_nat(to)));
          }
          assert int_of_nat(succ(from)) != int_of_nat(to);
          full_free_list_some_engaged(n, succ(from), to, i+1);
          some_engaged_over_bigger_list(n, succ(from), to, i);
          assert true == some_engaged(full_free_list_fp(len, i), succ(from), to);
          assert true == mem(int_of_nat(from) + INDEX_SHIFT, full_free_list_fp(len, i));
          consolidate_some_engaged(full_free_list_fp(len, i), from, to);
        }
    }
  }

  lemma void some_all_engaged(list<int> lst, nat to)
  requires true == some_engaged(lst, zero, to);
  ensures true == all_engaged(nil, lst, to) &*&
          true == all_engaged(lst, nil, to);
  {
    switch(to) {
      case zero: return;
      case succ(n):
        some_all_engaged(lst, n);
    }
  }

  lemma void full_free_list_all_engaged(nat len)
  requires true;
  ensures true == all_engaged(nil, full_free_list_fp(len, INDEX_SHIFT),
                              len);
  {
    if (len == zero) return;
    full_free_list_some_engaged(len, zero, len, INDEX_SHIFT);
    some_all_engaged(full_free_list_fp(len, INDEX_SHIFT), len);
  }

  lemma void weaker_lbound(list<int> l, int lb1, int lb2)
  requires true == forall(l, (lbounded)(lb1)) &*& lb2 < lb1;
  ensures true == forall(l, (lbounded)(lb2));
  {
    switch(l) {
      case nil: return;
      case cons(h,t):
        weaker_lbound(t, lb1, lb2);
    }
  }

  lemma void full_free_list_all_lbounded(nat len, int lb)
  requires true;
  ensures true == forall(full_free_list_fp(len, lb),
                         (lbounded)(lb));
  {
    switch(len) {
      case zero: return;
      case succ(n):
        full_free_list_all_lbounded(n, lb+1);
        weaker_lbound(full_free_list_fp(n, lb+1), lb+1, lb);
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
           true == forall(pref, (dbounded)(size));
  ensures dcellsp(cells + ind, int_of_nat(len)+1, ?lst) &*&
          free_listp(append(pref, lst), full_free_list_fp(len, ind+1), 1, ind) &*&
          true == forall(append(pref, lst), (dbounded)(size));
  {
    switch(len) {
      case zero:
        close dcellsp(cells + ind, 1, cons(dcell(1,1), nil));
        nth_append_r(pref, cons(dcell(1,1), nil), 0);
        forall_append(pref, cons(dcell(1,1), nil), (dbounded)(size));
        close free_listp(append(pref, cons(dcell(1,1), nil)), nil, 1, ind);
        return;
      case succ(n):
        open dcellsp(cells + ind, int_of_nat(len), empty_cells_seg(len, ind));
        assert dcellp(cells + ind, dcell(ind+1,ind+1));
        assert ind+1+int_of_nat(n) == ind+int_of_nat(len);
        mul_subst(ind+1+int_of_nat(n), ind+int_of_nat(len), sizeof(struct dchain_cell));
        forall_append(pref, cons(dcell(ind+1,ind+1), nil), (dbounded)(size));
        empty_dchain_produced_tail(cells, n, ind+1, size,
                                   append(pref,cons(dcell(ind+1,ind+1), nil)));
        assert dcellsp(cells+ind+1, int_of_nat(n)+1, ?lst_tail);
        assert free_listp(append(append(pref, cons(dcell(ind+1,ind+1),
                                              nil)), lst_tail),
                          full_free_list_fp(n, ind+2),
                          1, ind+1);
        close dcellsp(cells+ind, int_of_nat(len)+1,
                      cons(dcell(ind+1,ind+1), lst_tail));

        nth_append_r(pref, cons(dcell(ind+1,ind+1), lst_tail), 0);
        append_append_cons_to_append_cons(pref, dcell(ind+1,ind+1), lst_tail);
        close free_listp(append(pref, cons(dcell(ind+1,ind+1), lst_tail)),
                         full_free_list_fp(len, ind+1), 1, ind);
    }
  }

  lemma void empty_dchain_produced(struct dchain_cell* cells, int len)
  requires dcellp(cells, dcell(0,0)) &*& dcellsp(cells+1, len,
                                                 empty_cells_seg(nat_of_int(len), 1)) &*&
           dcellp(cells + len + 1, dcell(1,1)) &*&
           0 < len;
  ensures dcellsp(cells, len+2, ?lst) &*&
          true == forall(lst, (dbounded)(len+2)) &*&
          free_listp(lst, full_free_list_fp(nat_of_int(len), 2), 1, 1) &*&
          alloc_listp(lst, nil, 0, 0);
  {
    empty_dchain_produced_tail(cells, nat_of_int(len), 1, len+2,
                               cons(dcell(0,0),nil));
    assert dcellsp(cells+1, len+1, ?lst);
    close dcellsp(cells, len+2, cons(dcell(0,0), lst));
    close alloc_listp(cons(dcell(0,0), lst), nil, 0, 0);
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
  //@ full_free_list_all_engaged(nat_of_int(size));
  //@ full_free_list_all_lbounded(nat_of_int(size), INDEX_SHIFT);
  //@ close dchainip(empty_dchaini_fp(size), cells);
}

/*@
  lemma void short_circuited_free_list(list<dcell> cells, list<int> fl)
  requires free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*&
           nth(FREE_LIST_HEAD, cells) == dcell(_,1);
  ensures free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*& fl == nil;
  {
    switch(fl) {
      case nil: return;
      case cons(h,t):
        open free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD);
        close free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD);
    }
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
  lemma void non_empty_free_list(list<dcell> cells, list<int> fl)
  requires free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*&
           dchain_cell_get_next(nth(1, cells)) != 1;
  ensures free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*& fl != nil;
  {
    switch(fl) {
      case nil:
        open free_listp(cells, fl, FREE_LIST_HEAD, FREE_LIST_HEAD);
        return;
      case cons(h,t):
        return;
    }
  }
  @*/

/*@
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

  lemma void extract_heads(struct dchain_cell* cells, list<dcell> cls)
  requires dcellsp(cells, ?size, cls) &*& INDEX_SHIFT <= size;
  ensures dcellsp(cells+INDEX_SHIFT, size-2, drop(2,cls)) &*&
          dcellp(cells+ALLOC_LIST_HEAD, nth(ALLOC_LIST_HEAD, cls)) &*&
          dcellp(cells+FREE_LIST_HEAD, nth(FREE_LIST_HEAD, cls));
  {
    open dcellsp(cells, size, cls);
    open dcellsp(cells+1, size-1, tail(cls));
  }

  lemma void drop_add_one<t>(list<t> lst, int i)
  requires 0 <= i &*& i < length(lst);
  ensures drop(i, lst) == cons(nth(i, lst), drop(i + 1, lst));
  {
    switch(lst) {
      case nil: return;
      case cons(h,t):
        if (i != 0)
          drop_add_one(t, i-1);
    }
  }

  lemma void attach_heads(struct dchain_cell* cells, list<dcell> cls)
  requires dcellsp(cells+INDEX_SHIFT, length(cls)-INDEX_SHIFT,
                   drop(INDEX_SHIFT,cls)) &*&
           dcellp(cells+ALLOC_LIST_HEAD, nth(ALLOC_LIST_HEAD, cls)) &*&
           dcellp(cells+FREE_LIST_HEAD, nth(FREE_LIST_HEAD, cls)) &*&
           INDEX_SHIFT <= length(cls);
  ensures dcellsp(cells, length(cls), cls);
  {
    drop_add_one(cls, 1);
    close dcellsp(cells+1, length(cls)-1, drop(1,cls));
    drop_add_one(cls, 0);
    close dcellsp(cells, length(cls), cls);
  }

  lemma void extract_cell_body(struct dchain_cell* cells,
                               list<dcell> cls, int i)
  requires dcellsp(cells, ?size, cls) &*&
           0 <= i &*& i < size;
  ensures dcellsp(cells, i, take(i, cls)) &*&
          dcellp(cells+i, nth(i, cls)) &*&
          dcellsp(cells+i+1, size - i - 1, drop(i+1, cls));
  {
    open dcellsp(cells, size, cls);
    switch(cls) {
      case nil:
        return;
      case cons(h,t):
        if (i == 0) {
        } else {
          extract_cell_body(cells+1, t, i-1);
        }
    }
    close dcellsp(cells, i, take(i, cls));
  }

  lemma void extract_cell(struct dchain_cell* cells, list<dcell> cls, int i)
  requires dcellsp(cells+INDEX_SHIFT, ?size, drop(INDEX_SHIFT, cls)) &*&
           INDEX_SHIFT <= i &*& i < size + INDEX_SHIFT &*&
           INDEX_SHIFT <= length(cls);
  ensures dcellsp(cells+INDEX_SHIFT, i-INDEX_SHIFT,
                  take(i-INDEX_SHIFT, drop(INDEX_SHIFT, cls))) &*&
          dcellp(cells+i, nth(i, cls)) &*&
          dcellsp(cells+i+1, size - i + 1,
                  drop(i+1, cls)) &*&
          0 <= i*sizeof(struct dchain_cell) &*&
          i*sizeof(struct dchain_cell) <
             (size+INDEX_SHIFT)*sizeof(struct dchain_cell);
  {
    dcellsp_length(cells+INDEX_SHIFT);
    length_drop(INDEX_SHIFT, cls);
    assert(length(cls) == size + INDEX_SHIFT);
    extract_cell_body(cells+INDEX_SHIFT, drop(INDEX_SHIFT, cls),
                      i - INDEX_SHIFT);
    nth_drop(i - INDEX_SHIFT, INDEX_SHIFT, cls);
    drop_drop(i + 1 - INDEX_SHIFT, 2, cls);
    mul_mono_strict(i, size+INDEX_SHIFT,
                    sizeof(struct dchain_cell));
  }

  lemma void glue_cells_body(struct dchain_cell* cells, list<dcell> cls, int i)
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
          glue_cells_body(cells+1, t, i-1);
        }
        close dcellsp(cells, length(cls), cls);
    }
  }

  lemma void glue_cells(struct dchain_cell* cells, list<dcell> cls, int i)
  requires INDEX_SHIFT <= i &*& i < length(cls) &*&
           dcellsp(cells+INDEX_SHIFT, i-INDEX_SHIFT,
                   take(i-INDEX_SHIFT, drop(INDEX_SHIFT, cls))) &*&
           dcellp(cells+i, nth(i, cls)) &*&
           dcellsp(cells+i+1, length(cls) - i - 1, drop(i+1, cls));
  ensures dcellsp(cells+INDEX_SHIFT, length(cls)-INDEX_SHIFT,
                  drop(INDEX_SHIFT, cls));
  {
    length_drop(INDEX_SHIFT, cls);
    nth_drop(i - INDEX_SHIFT, INDEX_SHIFT, cls);
    drop_drop(i + 1 - INDEX_SHIFT, 2, cls);
    glue_cells_body(cells+INDEX_SHIFT, drop(INDEX_SHIFT, cls), i - INDEX_SHIFT);
  }
  @*/
/* @
  lemma void free_list_above_alloc(list<dcell> cls, list<int> fl, int ind)
  requires free_listp(cls, fl, FREE_LIST_HEAD, ind);
  ensures free_listp(cls, fl, FREE_LIST_HEAD, ind) &*&
          ALLOC_LIST_HEAD < dchain_cell_get_next(nth(ind, cls));
  {
    open free_listp(cls, fl, 1, ind);
    switch(fl) {
      case nil: break;
      case cons(h,t):
        open free_listp(cls, t, 1, h);
        close free_listp(cls, t, 1, h);
     };
     close free_listp(cls, fl, 1, ind);
  }
  @ */


/* @
  lemma void free_mem_symm(list<dcell> cls, list<int> fl,
                           int x, int i, int start)
  requires free_listp(cls, fl, start, i) &*& true == mem(x, fl);
  ensures free_listp(cls, fl, start, i) &*&
          dchain_cell_get_next(nth(x,cls)) ==
          dchain_cell_get_prev(nth(x,cls));
  {
    switch(fl) {
      case nil:
        return;
      case cons(h,t):
        open free_listp(cls, fl, start, i);
        if (h == x) {
          open free_listp(cls, t, start, h);
          close free_listp(cls, t, start, h);
        }
        else {
          free_mem_symm(cls, t, x, h, start);
        }
        close free_listp(cls, fl, start, i);
    }
  }

  lemma void alloc_mem_asymm(list<dcell> cls, list<int> al, int x, int i, int start)
  requires alloc_listp(cls, al, start, i) &*& true == mem(x, al);
  ensures alloc_listp(cls, al, start, i) &*&
          dchain_cell_get_next(nth(x, cls)) !=
          dchain_cell_get_prev(nth(x, cls));
  {
    switch(al) {
      case nil:
        return;
      case cons(h,t):
        open alloc_listp(cls, al, start, i);
        if (h == x) {
          open alloc_listp(cls, t, start, h);
          close alloc_listp(cls, t, start, h);
        } else {
          alloc_mem_asymm(cls, t, x, h, start);
        }
        close alloc_listp(cls, al, start, i);
    }
  }
  @ */
/*@

  lemma void free_alloc_disjoint(list<int> al, list<int> fl, int x, nat size)
  requires true == all_engaged(al, fl, size) &*&
           INDEX_SHIFT <= x &*& x < int_of_nat(size) + INDEX_SHIFT;
  ensures mem(x, fl) ?
          false == mem(x, al) :
          true == mem(x, al);
  {
    switch(size) {
      case zero: return;
      case succ(n):
        if (x == INDEX_SHIFT + int_of_nat(n)) {
        } else {
          free_alloc_disjoint(al, fl, x, n);
        }
    }
  }
  @*/

/*@
  lemma void all_engaged_remove_unrelevant(list<int> al, list<int> fl,
                                           int x, nat size)
  requires true == all_engaged(al, fl, size) &*&
           int_of_nat(size)+INDEX_SHIFT <= x;
  ensures true == all_engaged(al, remove(x, fl), size) &*&
          true == all_engaged(remove(x, al), fl, size);
  {
    switch(size) {
      case zero:
        return;
      case succ(n):
        all_engaged_remove_unrelevant(al, fl, x, n);
        neq_mem_remove(int_of_nat(n)+INDEX_SHIFT, x, al);
        neq_mem_remove(int_of_nat(n)+INDEX_SHIFT, x, fl);
    }
  }
@*/

/*@

  lemma void shift_inds_mem(list<int> l, int shift, int x)
  requires true;
  ensures mem(x, shift_inds_fp(l, shift)) == mem(x-shift, l);
  {
    switch(l) {
      case nil: return;
      case cons(h,t):
        if (x-shift != h)
          shift_inds_mem(t, shift, x);
    }
  }
  @*/

/*@
  lemma void alloc_prev_alloc_member(list<dcell> cls, list<int> al,
                                     int start, int x, int i)
  requires alloc_listp(cls, al, start, i) &*&
           nth(start, cls) == dcell(x,_) &*& x != i;
  ensures alloc_listp(cls, al, start, i) &*& true == mem(x, al);
  {
    open alloc_listp(cls, al, start, i);
    switch(al) {
      case nil:
        assert x == i;
      case cons(h,t):
        if (h != x) alloc_prev_alloc_member(cls, t, start, x, h);
    }
    close alloc_listp(cls, al, start, i);
  }
@*/


/*@
  lemma void free_list_update_unrelevant(list<dcell> cls, list<int> fl,
                                         int start, int i,
                                         int x, dcell val)
  requires free_listp(cls, fl, start, i) &*& false == mem(x, fl) &*&
           i != x &*& 0 <= x &*& x < length(cls);
  ensures free_listp(update(x, val, cls), fl, start, i);
  {
    open free_listp(cls, fl, start, i);
    switch(fl) {
      case nil:
        break;
      case cons(h,t):
        nth_update(0, x, val, cls);
        free_list_update_unrelevant(cls, t, start, h, x, val);
    }
    nth_update_unrelevant(i, x, val, cls);
    close free_listp(update(x, val, cls), fl, start, i);
  }

  lemma void lbounded_then_start_nonmem(list<int> fl, int start)
  requires true == forall(fl, (lbounded)(INDEX_SHIFT)) &*&
           start < INDEX_SHIFT;
  ensures false == mem(start, fl);
  {
    switch(fl){
      case nil: return;
      case cons(h,t):
        lbounded_then_start_nonmem(t, start);
    }
  }

  lemma void remove_first_free_cell(list<dcell> cls, list<int> fl, int start)
  requires free_listp(cls, fl, start, start) &*&
           nth(start, cls) == dcell(?p, ?n) &*&
           p == n &*& p != start &*&
           nth(p, cls) == dcell(?pp, ?pn) &*&
           fl == cons(p, ?flt) &*&
           true == forall(fl, (lbounded)(INDEX_SHIFT)) &*&
           0 <= start &*& start < INDEX_SHIFT &*&
           INDEX_SHIFT <= length(cls);
  ensures free_listp(update(start, dcell(pn, pn), cls), flt, start, start);
  {
    open free_listp(cls, fl, start, start);
    lbounded_then_start_nonmem(flt, start);
    free_list_update_unrelevant(cls, flt, start, p, start, dcell(pn, pn));
    open free_listp(update(start, dcell(pn,pn), cls), flt, start, p);
    nth_update(start, start, dcell(pn, pn), cls);
    nth_update_unrelevant(p, start, dcell(pn, pn), cls);
    close free_listp(update(start, dcell(pn,pn), cls), flt, start, start);
  }
  @*/

/*@

  lemma void insert_to_empty_alloc_list(list<dcell> cls, int start,
                                        int ins)
  requires alloc_listp(cls, nil, start, start) &*&
           nth(start, cls) == dcell(start, start) &*&
           0 <= start &*& start < INDEX_SHIFT &*&
           INDEX_SHIFT <= ins &*& ins < length(cls) &*&
           INDEX_SHIFT <= length(cls) &*&
           ins != start;
  ensures alloc_listp(update(start, dcell(ins, ins),
                       update(ins, dcell(start, start), cls)),
                      cons(ins, nil),
                      start,
                      start);
  {
    open alloc_listp(cls, nil, start, start);
    nth_update(ins, ins, dcell(start, start), cls);
    nth_update(start, start, dcell(ins, ins), update(ins, dcell(start, start), cls));
    nth_update(ins, start, dcell(ins, ins), update(ins, dcell(start, start), cls));
    close alloc_listp(update(start, dcell(ins, ins),
                       update(ins, dcell(start, start), cls)),
                      nil,
                      start,
                      ins);
    close alloc_listp(update(start, dcell(ins, ins),
                       update(ins, dcell(start, start), cls)),
                      cons(ins, nil),
                      start,
                      start);
  }
  @*/

/*@
  lemma void two_alloc_lists_equal(list<dcell> cls, list<int> al1, list<int> al2,
                                   int start, int i)
  requires alloc_listp(cls, al1, start, i) &*& alloc_listp(cls, al2, start, i) &*&
           false == mem(start, al1) &*& false == mem(start, al2);
  ensures alloc_listp(cls, al1, start, i) &*& al1 == al2;
  {
    open alloc_listp(cls, al1, start, i);
    open alloc_listp(cls, al2, start, i);
    switch(al1) {
      case nil:
        assert al2 == nil;
        break;
      case cons(h1,t1):
        assert al2 == cons(?h2,?t2);
        assert h1 == h2;
        two_alloc_lists_equal(cls, t1, t2, start, h1);
        break;
    }
    close alloc_listp(cls, al1, start, i);
  }

  lemma void duplicate_alloc_listp(list<dcell> cls, list<int> al, int start, int i)
  requires alloc_listp(cls, al, start, i);
  ensures alloc_listp(cls, al, start, i) &*& alloc_listp(cls, al, start, i);
  {
    open alloc_listp(cls, al, start, i);
    switch(al) {
      case nil: break;
      case cons(h,t):
        duplicate_alloc_listp(cls, t, start, h);
    }
    close alloc_listp(cls, al, start, i);
    close alloc_listp(cls, al, start, i);
  }

  lemma list<int> alloc_list_strip_to_el(list<dcell> cls, list<int> al,
                                         int start, int i, int el)
  requires alloc_listp(cls, al, start, i) &*& true == mem(el, al) &*&
           false == mem(start, al);
  ensures alloc_listp(cls, result, start, el) &*&
          length(result) < length(al) &*&
          false == mem(start, result);
  {
    switch(al) {
      case nil: return;
      case cons(h,t):
        open alloc_listp(cls, al, start, i);
        if (h == el) {
          return t;
        } else
          return alloc_list_strip_to_el(cls, t, start, h, el);
    }
  }

  lemma void alloc_list_no_dups_head(list<dcell> cls, list<int> al,
                                     int start, int i)
  requires alloc_listp(cls, al, start, i) &*& al == cons(?ah,?at) &*&
           false == mem(start, al);
  ensures alloc_listp(cls, al, start, i) &*& false == mem(ah, at);
  {
    if (mem(ah, at)) {
      switch(al) {
        case nil: return;
        case cons(h,t):
          assert(h == ah);
          duplicate_alloc_listp(cls, al, start, i);
          open alloc_listp(cls, cons(ah,at), start, i);
          open alloc_listp(cls, cons(ah,at), start, i);
          //assert alloc_listp(cls, al, start, ah);
          list<int> nal = alloc_list_strip_to_el(cls, at, start, ah, ah);
          two_alloc_lists_equal(cls, at, nal, start, ah);
      }
    }
  }

  lemma void alloc_list_no_dups(list<dcell> cls, list<int> al,
                                int start, int i, int el)
  requires alloc_listp(cls, al, start, i) &*&
           false == mem(start, al);
  ensures alloc_listp(cls, al, start, i) &*&
          false == mem(el, remove(el, al));
  {
    switch(al) {
      case nil: return;
      case cons(h,t):
        if (h == el) {
          alloc_list_no_dups_head(cls, al, start, i);
        } else {
          open alloc_listp(cls, al, start, i);
          alloc_list_no_dups(cls, t, start, h, el);
          close alloc_listp(cls, al, start, i);
        }
    }
  }
  @*/

/*@
  lemma void last_alloc_list_mem(list<dcell> cls, list<int> al, int start, int i)
  requires alloc_listp(cls, al, start, i) &*&
           nth(start, cls) == dcell(?prev,?next) &*&
           al != nil;
  ensures alloc_listp(cls, al, start, i) &*& true == mem(prev, al);
  {
    open alloc_listp(cls, al, start, i);
    switch(al) {
      case nil: return;
      case cons(h,t):
        if (t == nil) {
          open alloc_listp(cls, t, start, h);
          assert h == prev;
          close alloc_listp(cls, t, start, h);
        } else
          last_alloc_list_mem(cls, t, start, h);
    }
    close alloc_listp(cls, al, start, i);
  }

  lemma void insert_alloc_list_iter(list<dcell> cls, list<int> al, int start,
                                    int ins, int i)
  requires alloc_listp(cls, al, start, i) &*&
           true == forall(cls, (dbounded)(length(cls))) &*&
           nth(start, cls) == dcell(?old_last, ?old_first) &*&
           nth(old_last, cls) == dcell(?old_last_prev, start) &*&
           0 <= start &*& start < INDEX_SHIFT &*&
           INDEX_SHIFT <= ins &*& ins < length(cls) &*&
           ins != start &*& ins != i &*&
           false == mem(ins, al) &*&
           al != nil &*&
           false == mem(start, al) &*&
           false == mem(i, al);
  ensures alloc_listp(update(start, dcell(ins, old_first),
                       update(ins, dcell(old_last, start),
                        update(old_last, dcell(old_last_prev, ins), cls))),
                      append(al, cons(ins, nil)),
                      start,
                      i);
  {
    switch(al) {
      case nil: return;
      case cons(h,t):
        last_alloc_list_mem(cls, al, start, i);
        alloc_list_no_dups_head(cls, al, start, i);
        open alloc_listp(cls, al, start, i);
        if (ins == old_last) {
          assert true == mem(old_last, al);
        }
        assert ins != old_last;
        assert start != old_last;
        assert ins != start;
        switch(t) {
          case nil:
            open alloc_listp(cls, t, start, h);
            assert h == old_last;
            nth_update(ins, ins, dcell(old_last, start),
                       update(old_last, dcell(old_last_prev, ins), cls));
            nth_update_unrelevant(ins, start, dcell(ins, old_first),
                                  update(ins, dcell(old_last, start),
                                   update(old_last, dcell(old_last_prev, ins), cls)));
            close alloc_listp(update(start, dcell(ins, old_first),
                               update(ins, dcell(old_last, start),
                                update(old_last, dcell(old_last_prev, ins), cls))),
                              nil,
                              start,
                              ins);
            forall_nth(cls, (dbounded)(length(cls)), start);
            assert 0 <= old_last &*& old_last < length(cls);
            nth_update(old_last, old_last, dcell(old_last_prev, ins), cls);
            nth_update_unrelevant(old_last, ins, dcell(old_last, start),
                                  update(old_last, dcell(old_last_prev, ins), cls));
            nth_update_unrelevant(old_last, start, dcell(ins, old_first),
                                  update(ins, dcell(old_last, start),
                                   update(old_last, dcell(old_last_prev, ins), cls)));
            close alloc_listp(update(start, dcell(ins, old_first),
                               update(ins, dcell(old_last, start),
                                update(old_last, dcell(old_last_prev, ins), cls))),
                              cons(ins, nil),
                              start,
                              h);
            break;
          case cons(th, tt):
            if (h == old_last) {
              open alloc_listp(cls, t, start, h);
              assert (h != old_last);
              close alloc_listp(cls, t, start, h);
            }
            assert (h != old_last);
            assert false == mem(h, t);
            insert_alloc_list_iter(cls, t, start, ins, h);
            assert h != start;
            assert h != ins;
            nth_update_unrelevant(h, old_last, dcell(old_last_prev, ins), cls);
            nth_update_unrelevant(h, ins, dcell(old_last, start),
                                  update(old_last, dcell(old_last_prev, ins), cls));
            nth_update_unrelevant(h, start, dcell(ins, old_first),
                                  update(ins, dcell(old_last, start),
                                    update(old_last, dcell(old_last_prev, ins), cls)));
            break;
        }
        if (i == old_last) {
          assert true == mem(old_last, al);
          assert false == mem(i, al);
        }
        assert i != ins;
        assert i != old_last;
        if (i == start) {
          nth_update(i, start, dcell(ins, old_first),
                     update(ins, dcell(old_last, start),
                      update(old_last, dcell(old_last_prev, ins), cls)));
        } else {
          nth_update_unrelevant(i, old_last, dcell(old_last_prev, ins), cls);
          nth_update_unrelevant(i, ins, dcell(old_last, start),
                                update(old_last, dcell(old_last_prev, ins), cls));
          nth_update_unrelevant(i, start, dcell(ins, old_first),
                                update(ins, dcell(old_last, start),
                                 update(old_last, dcell(old_last_prev, ins), cls)));
        }

        close alloc_listp(update(start, dcell(ins, old_first),
                          update(ins, dcell(old_last, start),
                            update(old_last, dcell(old_last_prev, ins), cls))),
                          append(al, cons(ins, nil)),
                          start,
                          i);
    }
  }

  lemma void alloc_list_last_next(list<dcell> cls, list<int> al,
                                  int start, int i)
  requires alloc_listp(cls, al, start, i) &*&
           nth(start, cls) == dcell(?last, ?first);
  ensures alloc_listp(cls, al, start, i) &*&
          nth(last, cls) == dcell(_, start);
  {
    open alloc_listp(cls, al, start, i);
    switch(al) {
      case nil:
      case cons(h,t):
        alloc_list_last_next(cls, t, start, h);
    }
    close alloc_listp(cls, al, start, i);
  }

  lemma void insert_alloc_list(list<dcell> cls, list<int> al, int start,
                               int ins)
  requires alloc_listp(cls, al, start, start) &*&
           true == forall(cls, (dbounded)(length(cls))) &*&
           nth(start, cls) == dcell(?old_last, ?old_first) &*&
           nth(old_last, cls) == dcell(?old_last_prev, ?y) &*&
           0 <= start &*& start < INDEX_SHIFT &*&
           INDEX_SHIFT <= ins &*& ins < length(cls) &*&
           ins != start &*& false == mem(ins, al) &*&
           al != nil &*&
           false == mem(start, al);
  ensures alloc_listp(update(start, dcell(ins, old_first),
                       update(ins, dcell(old_last, start),
                        update(old_last, dcell(old_last_prev, ins), cls))),
                      append(al, cons(ins, nil)),
                      start,
                      start);
  {
    alloc_list_last_next(cls, al, start, start);
    assert(y == start);
    insert_alloc_list_iter(cls, al, start, ins, start);
  }
  @*/

/*@
  lemma void head_is_not_mem(list<int> l, int head, int brd)
  requires true == forall(l, (lbounded)(brd)) &*& head < brd;
  ensures false == mem(head, l);
  {
    switch(l) {
      case nil: return;
      case cons(h,t):
        head_is_not_mem(t, head, brd);
    }
  }
  @*/

/*@
  lemma void alloc_list_update_unrelevant(list<dcell> cls, list<int> al,
                                          int start, int ind, dcell val,
                                          int i)
  requires alloc_listp(cls, al, start, i) &*&
           ind != i &*& ind != start &*&
           false == mem(ind, al);
  ensures alloc_listp(update(ind, val, cls), al, start, i);
  {
    open alloc_listp(cls, al, start, i);
    switch(al) {
      case nil:
        nth_update_unrelevant(start, ind, val, cls);
        break;
      case cons(h,t):
        alloc_list_update_unrelevant(cls, t, start, ind, val, h);
        nth_update_unrelevant(h, ind, val, cls);
    }
    nth_update_unrelevant(i, ind, val, cls);
    close alloc_listp(update(ind, val, cls), al, start, i);
  }
  @*/

/*@
  lemma void two_free_lists_equal(list<dcell> cls, list<int> fl1, list<int> fl2,
                                  int start, int i)
  requires free_listp(cls, fl1, start, i) &*& free_listp(cls, fl2, start, i) &*&
           false == mem(start, fl1) &*& false == mem(start, fl2);
  ensures free_listp(cls, fl1, start, i) &*& fl1 == fl2;
  {
    open free_listp(cls, fl1, start, i);
    open free_listp(cls, fl2, start, i);
    switch(fl1) {
      case nil:
        assert fl2 == nil;
        break;
      case cons(h1,t1):
        assert fl2 == cons(?h2,?t2);
        assert h1 == h2;
        two_free_lists_equal(cls, t1, t2, start, h1);
        break;
    }
    close free_listp(cls, fl1, start, i);
  }

  lemma void duplicate_free_listp(list<dcell> cls, list<int> fl, int start, int i)
  requires free_listp(cls, fl, start, i);
  ensures free_listp(cls, fl, start, i) &*& free_listp(cls, fl, start, i);
  {
    open free_listp(cls, fl, start, i);
    switch(fl) {
      case nil: break;
      case cons(h,t):
        duplicate_free_listp(cls, t, start, h);
    }
    close free_listp(cls, fl, start, i);
    close free_listp(cls, fl, start, i);
  }

  lemma list<int> free_list_strip_to_el(list<dcell> cls, list<int> fl,
                                         int start, int i, int el)
  requires free_listp(cls, fl, start, i) &*& true == mem(el, fl) &*&
           false == mem(start, fl);
  ensures free_listp(cls, result, start, el) &*&
          length(result) < length(fl) &*&
          false == mem(start, result);
  {
    switch(fl) {
      case nil: return;
      case cons(h,t):
        open free_listp(cls, fl, start, i);
        if (h == el) {
          return t;
        } else
          return free_list_strip_to_el(cls, t, start, h, el);
    }
  }

  lemma void free_list_no_dups_head(list<dcell> cls, list<int> fl,
                                     int start, int i)
  requires free_listp(cls, fl, start, i) &*& fl == cons(?ah,?at) &*&
           false == mem(start, fl);
  ensures free_listp(cls, fl, start, i) &*& false == mem(ah, at);
  {
    if (mem(ah, at)) {
      switch(fl) {
        case nil: return;
        case cons(h,t):
          assert(h == ah);
          duplicate_free_listp(cls, fl, start, i);
          open free_listp(cls, cons(ah,at), start, i);
          open free_listp(cls, cons(ah,at), start, i);
          //assert free_listp(cls, fl, start, ah);
          list<int> nfl = free_list_strip_to_el(cls, at, start, ah, ah);
          two_free_lists_equal(cls, at, nfl, start, ah);
      }
    }
  }

  lemma void free_list_no_dups(list<dcell> cls, list<int> fl,
                                int start, int i, int el)
  requires free_listp(cls, fl, start, i) &*&
           false == mem(start, fl);
  ensures free_listp(cls, fl, start, i) &*&
          false == mem(el, remove(el, fl));
  {
    switch(fl) {
      case nil: return;
      case cons(h,t):
        if (h == el) {
          free_list_no_dups_head(cls, fl, start, i);
        } else {
          open free_listp(cls, fl, start, i);
          free_list_no_dups(cls, t, start, h, el);
          close free_listp(cls, fl, start, i);
        }
    }
  }
  @*/

/*@
lemma void move_cell_to_alloc_engaged(list<int> al, list<int> fl, nat size)
requires true == all_engaged(al, fl, size) &*& fl == cons(?fh,?ft) &*&
         false == mem(fh,ft);
ensures true == all_engaged(append(al, cons(fh, nil)), ft, size);
{
  switch(size) {
    case zero: return;
    case succ(n):
      move_cell_to_alloc_engaged(al, fl, n);
      if (int_of_nat(n) + INDEX_SHIFT == fh) {
        assert true == mem(int_of_nat(n) + INDEX_SHIFT, append(al, cons(fh, nil)));
        assert false == mem(int_of_nat(n) + INDEX_SHIFT, ft);
      } else {
      }
  }
}
@*/

/*@
  lemma void shift_inds_append(list<int> al, int i, list<int> allocd)
  requires al == shift_inds_fp(allocd, INDEX_SHIFT);
  ensures append(al, cons(i, nil)) ==
          shift_inds_fp(append(allocd, cons(i-INDEX_SHIFT, nil)), INDEX_SHIFT);
  {
    switch(al){
      case nil:
        switch(allocd) {
          case nil: return;
          case cons(x,y):
            return;
        }
      case cons(h,t):
        switch(allocd) {
          case nil: return;
          case cons(all_h, all_t):
            shift_inds_append(t, i, all_t);
        }
    }
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
              0 <= ni &*& ni < dchaini_irange_fp(dc) &*&
              false == dchaini_allocated_fp(dc, ni) &*&
              dchainip(dchaini_allocate_fp(dc, ni), cells))); @*/
{
  //@ open dchainip(dc, cells);
  //@ int size = dchaini_irange_fp(dc);
  //@ assert 0 < size;
  //@ assert dcellsp(cells, size + INDEX_SHIFT, ?cls);
  //@ dcellsp_length(cells);
  //@ assert free_listp(cls, ?fl, 1, 1);
  //@ assert alloc_listp(cls, ?al, 0, 0);
  /* No more empty cells. */
  //@ mul_nonnegative(size, sizeof(struct dchain_cell));
  //@ dcells_limits(cells);
  //@ extract_heads(cells, cls);
  struct dchain_cell* fl_head = cells + FREE_LIST_HEAD;
  struct dchain_cell* al_head = cells + ALLOC_LIST_HEAD;
  int allocated = fl_head->next;
  if (allocated == FREE_LIST_HEAD)
  {
    //@ attach_heads(cells, cls);
    //@ short_circuited_free_list(cls, fl);
    //@ assert(size <= length(al));
    //@ shift_inds_len(dchaini_alist_fp(dc), INDEX_SHIFT);
    //@ assert(size <= length(dchaini_alist_fp(dc)));
    //@ close dchainip(dc, cells);
    //@ assert true == dchaini_out_of_space_fp(dc);
    return 0;
  }
  //@ non_empty_free_list(cls, fl);
  //@ open free_listp(cls, fl, 1, 1);
  //@ assert(true == mem(allocated, fl));
  //@ close free_listp(cls, fl, 1, 1);

  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD);
  //@ assert 0 <= allocated &*& allocated < size + INDEX_SHIFT;
  //@ assert FREE_LIST_HEAD != allocated;
  //@ dcells_limits(cells+INDEX_SHIFT);
  //@ extract_cell(cells, cls, allocated);
  struct dchain_cell* allocp = cells + allocated;
  /* Extract the link from the "empty" chain. */
  fl_head->next = allocp->next;
  fl_head->prev = fl_head->next;

  /* Add the link to the "new"-end "alloc" chain. */
  allocp->next = ALLOC_LIST_HEAD;
  allocp->prev = al_head->prev;
  //@ dcell nalloc = dcell(dchain_cell_get_prev(nth(ALLOC_LIST_HEAD,cls)),ALLOC_LIST_HEAD);
  //@ int allocpnext = dchain_cell_get_next(nth(allocated, cls));
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), allocated);
  //@ dcell n_fl_head = dcell(allocpnext,allocpnext);
  //@ list<dcell> ncls = update(FREE_LIST_HEAD, n_fl_head, update(allocated, nalloc, cls));
  //@ drop_update_unrelevant(INDEX_SHIFT, FREE_LIST_HEAD, n_fl_head, update(allocated, nalloc, cls));
  //@ drop_update_relevant(INDEX_SHIFT, allocated, nalloc, cls);
  //@ take_update_unrelevant(allocated-INDEX_SHIFT, allocated-INDEX_SHIFT, nalloc, drop(INDEX_SHIFT, cls));
  //@ drop_update_unrelevant(allocated+1, FREE_LIST_HEAD, n_fl_head, update(allocated, nalloc, cls));
  //@ drop_update_unrelevant(allocated+1, allocated, nalloc, cls);
  //@ glue_cells(cells, ncls, allocated);
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD);
  //@ assert 0 <= al_head->prev;
  //@ dcells_limits(cells+INDEX_SHIFT);
  //@ int last_alloc = al_head->prev;
  //@ head_is_not_mem(al, ALLOC_LIST_HEAD, INDEX_SHIFT);
  //@ head_is_not_mem(al, FREE_LIST_HEAD, INDEX_SHIFT);
  //@ head_is_not_mem(fl, ALLOC_LIST_HEAD, INDEX_SHIFT);
  //@ head_is_not_mem(fl, FREE_LIST_HEAD, INDEX_SHIFT);
  /*@ if (al == nil) {
        open alloc_listp(cls, nil, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
        assert last_alloc == ALLOC_LIST_HEAD;
        close alloc_listp(cls, nil, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
      } else {
        last_alloc_list_mem(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
        assert true == mem(last_alloc, al);
        assert false == mem(FREE_LIST_HEAD, al);
        assert last_alloc != FREE_LIST_HEAD;
        assert last_alloc != ALLOC_LIST_HEAD;
        note(0 < al_head->prev);
        assert INDEX_SHIFT <= al_head->prev;
        extract_cell(cells, ncls, last_alloc);
        alloc_prev_alloc_member(cls, al, ALLOC_LIST_HEAD,
                                last_alloc, ALLOC_LIST_HEAD);
        assert true == mem(last_alloc, al);
      }
    @*/
  struct dchain_cell* alloc_head_prevp = cells + al_head->prev;
  alloc_head_prevp->next = allocated;
  al_head->prev = allocated;
  //@ assert(last_alloc != FREE_LIST_HEAD);
  //@ assert true == mem(allocated, fl);
  //@ if (last_alloc == allocated) { free_alloc_disjoint(al, fl, allocated, nat_of_int(size));}
  //@ assert(nth(last_alloc, cls) == nth(last_alloc, ncls));
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), last_alloc);
  /*@
    if (al == nil) {
      dcell n_al_head = dcell(allocated, allocated);
      list<dcell> rcls = update(ALLOC_LIST_HEAD, n_al_head, ncls);
      drop_update_unrelevant(INDEX_SHIFT, ALLOC_LIST_HEAD, n_al_head, ncls);
      attach_heads(cells, rcls);
    } else {
      dcell n_last_alloc = dcell(dchain_cell_get_prev(nth(last_alloc, cls)),allocated);
      dcell n_al_head = dcell(allocated, dchain_cell_get_next(nth(ALLOC_LIST_HEAD,cls)));
      list<dcell> rcls = update(ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls));
      drop_update_unrelevant(INDEX_SHIFT, ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls));
      drop_update_relevant(INDEX_SHIFT, last_alloc, n_last_alloc, ncls);
      take_update_unrelevant(last_alloc-INDEX_SHIFT, last_alloc-INDEX_SHIFT, n_last_alloc, drop(INDEX_SHIFT, ncls));
      drop_update_unrelevant(last_alloc+1, ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls));
      drop_update_unrelevant(last_alloc+1, last_alloc, n_last_alloc, ncls);
      glue_cells(cells, rcls, last_alloc);
      attach_heads(cells, rcls);
    }
    @*/


  *index = allocated - INDEX_SHIFT;
  //@ length_tail(fl);
  //@ shift_inds_len(dchaini_alist_fp(dc), INDEX_SHIFT);
  //@ assert(length(dchaini_alist_fp(dc)) != size);

  //@ free_alloc_disjoint(al, fl, allocated, nat_of_int(size));
  //@ assert(false == mem(allocated, al));
  //@ shift_inds_mem(dchaini_alist_fp(dc), INDEX_SHIFT, allocated);
  //@ assert(false == mem(allocated - INDEX_SHIFT, dchaini_alist_fp(dc)));

  //@ assert true == dbounded(size+INDEX_SHIFT, nalloc);
  //@ assert true == dbounded(size+INDEX_SHIFT, n_fl_head);
  /*@ {
    free_list_no_dups_head(cls, fl, FREE_LIST_HEAD, FREE_LIST_HEAD);
    assert false == mem(allocated, tail(fl));
    } @*/

  /*@
    if (al == nil) {
      forall_update(cls, (dbounded)(size+INDEX_SHIFT), allocated, nalloc);
      forall_update(update(allocated, nalloc, cls),
                    (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD, n_fl_head);
      forall_update(ncls, (dbounded)(size+INDEX_SHIFT),
                    ALLOC_LIST_HEAD, dcell(allocated, allocated));
      update_update(cls, FREE_LIST_HEAD, n_fl_head, allocated, nalloc);
      alloc_list_update_unrelevant(cls, al, ALLOC_LIST_HEAD,
                                   FREE_LIST_HEAD, n_fl_head,
                                   ALLOC_LIST_HEAD);
      insert_to_empty_alloc_list(update(FREE_LIST_HEAD, n_fl_head, cls),
                                 ALLOC_LIST_HEAD, allocated);

      remove_first_free_cell(cls, fl, FREE_LIST_HEAD);
      free_list_update_unrelevant(update(FREE_LIST_HEAD, n_fl_head, cls),
                                  tail(fl), FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  allocated, nalloc);
      free_list_update_unrelevant(update(allocated, nalloc,
                                   update(FREE_LIST_HEAD, n_fl_head, cls)),
                                  tail(fl), FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  ALLOC_LIST_HEAD, dcell(allocated, allocated));
    } else {
      dcell n_last_alloc = dcell(dchain_cell_get_prev(nth(last_alloc, cls)),allocated);
      dcell n_al_head = dcell(allocated, dchain_cell_get_next(nth(ALLOC_LIST_HEAD,cls)));
      forall_update(cls, (dbounded)(size+INDEX_SHIFT), allocated, nalloc);
      forall_update(update(allocated, nalloc, cls),
                    (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD, n_fl_head);
      forall_update(ncls, (dbounded)(size+INDEX_SHIFT),
                    last_alloc, n_last_alloc);
      forall_update(update(last_alloc, n_last_alloc, ncls),
                    (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD, n_al_head);
      update_update(update(allocated, nalloc, cls), 1, n_fl_head, last_alloc, n_last_alloc);
      update_update(update(last_alloc, n_last_alloc,
                     update(allocated, nalloc, cls)), 0, n_al_head, 1, n_fl_head);
      update_update(cls, allocated, nalloc, last_alloc, n_last_alloc);
      insert_alloc_list(cls, al, ALLOC_LIST_HEAD, allocated);
      alloc_list_update_unrelevant(update(ALLOC_LIST_HEAD, n_al_head,
                                    update(allocated, nalloc,
                                     update(last_alloc, n_last_alloc, cls))),
                                   append(al, cons(allocated, nil)),
                                   ALLOC_LIST_HEAD,
                                   FREE_LIST_HEAD, n_fl_head,
                                   ALLOC_LIST_HEAD);
      update_update(update(last_alloc, n_last_alloc, cls),
                    allocated, nalloc, ALLOC_LIST_HEAD, n_al_head);
      update_update(update(0, n_al_head,
                     update(last_alloc, n_last_alloc, cls)),
                    allocated, nalloc, FREE_LIST_HEAD, n_fl_head);
      {
        assert true == mem(last_alloc, al);
        free_alloc_disjoint(al, fl, last_alloc, nat_of_int(size));
        assert(head(fl) == allocated);
        free_list_update_unrelevant(cls, fl, FREE_LIST_HEAD,
                                    FREE_LIST_HEAD,
                                    last_alloc, n_last_alloc);
        free_list_update_unrelevant(update(last_alloc, n_last_alloc, cls),
                                    fl, FREE_LIST_HEAD,
                                    FREE_LIST_HEAD,
                                    ALLOC_LIST_HEAD, n_al_head);
        remove_first_free_cell(update(ALLOC_LIST_HEAD, n_al_head,
                                update(last_alloc, n_last_alloc, cls)),
                              fl, FREE_LIST_HEAD);
        free_list_update_unrelevant(update(FREE_LIST_HEAD, n_fl_head,
                                     update(ALLOC_LIST_HEAD, n_al_head,
                                      update(last_alloc, n_last_alloc, cls))),
                                    tail(fl), FREE_LIST_HEAD,
                                    FREE_LIST_HEAD,
                                    allocated, nalloc);
      }
    }
    @*/
  //@ move_cell_to_alloc_engaged(al, fl, nat_of_int(size));
  //@ assert true == forall(cons(allocated, nil), (lbounded)(INDEX_SHIFT));
  //@ forall_append(al, cons(allocated, nil), (lbounded)(INDEX_SHIFT));
  //@ assert true == forall(tail(fl), (lbounded)(INDEX_SHIFT));
  //@ shift_inds_append(al, allocated, dchaini_alist_fp(dc));

  //@ close dchainip(dchaini_allocate_fp(dc, allocated-INDEX_SHIFT), cells);
  return 1;
}

/*@
  lemma void symm_non_alloc_iter(list<dcell> cls, list<int> al,
                                 int start, int x, int i)
  requires alloc_listp(cls, al, start, i) &*&
           nth(x, cls) == dcell(?p,?n) &*& p == n &*& p != start &*&
           false == mem(i, al) &*& false == mem(start, al);
  ensures alloc_listp(cls, al, start, i) &*&
          false == mem(x, al);
  {
    switch(al) {
      case nil: break;
      case cons(h,t):
        open alloc_listp(cls, al, start, i);
        if (h == x) {
          open alloc_listp(cls, t, start, h);
          switch(t) {
            case nil: break;
            case cons(th,tt):
              assert(th == i);
              assert(true == mem(i, al));
          }
          close alloc_listp(cls, t, start, h);
        }
        else {
          close alloc_listp(cls, al, start, i);
          alloc_list_no_dups_head(cls, al, start, i);
          open alloc_listp(cls, al, start, i);
          symm_non_alloc_iter(cls, t, start, x, h);
        }
        close alloc_listp(cls, al, start, i);
        break;
    }
  }

  lemma void symm_non_alloc(list<dcell> cls, list<int> al, int start, int x)
  requires alloc_listp(cls, al, start, start) &*&
           nth(x, cls) == dcell(?p,?n) &*& p == n &*& p != start &*&
           false == mem(start, al);
  ensures alloc_listp(cls, al, start, start) &*& false == mem(x, al);
  {
    symm_non_alloc_iter(cls, al, start, x, start);
  }
  @*/

/*@
  lemma void asymm_non_in_free_list(list<dcell> cls, list<int> fl,
                                    int start, int x, int i)
  requires free_listp(cls, fl, start, i) &*&
           nth(x, cls) == dcell(?p,?n) &*& p != n;
  ensures free_listp(cls, fl, start, i) &*& false == mem(x, fl);
  {
    open free_listp(cls, fl, start, i);
    switch(fl) {
      case nil: break;
      case cons(h,t):
        asymm_non_in_free_list(cls, t, start, x, h);
        if (h == x) {
          open free_listp(cls, t, start, h);
          assert p == n;
          close free_listp(cls, t, start, h);
        }
    }
    close free_listp(cls, fl, start, i);
  }

  lemma void next_fl_member(list<dcell> cls, list<int> fl,
                            int start, int x, int i)
  requires free_listp(cls, fl, start, i) &*&
           nth(x, cls) == dcell(?p,?n) &*&
           n != start &*&
           true == mem(x, fl);
  ensures free_listp(cls, fl, start, i) &*&
          true == mem(n, fl) &*& p == n;
  {
    switch(fl) {
      case nil:
        return;
      case cons(h,t):
        open free_listp(cls, fl, start, i);
        if (h == x) {
          open free_listp(cls, t, start, h);
          switch(t) {
            case nil: break;
            case cons(th,tt):
              open free_listp(cls, tt, start, th);
              close free_listp(cls, tt, start, th);
          }
          close free_listp(cls, t, start, h);
        } else {
          next_fl_member(cls, t, start, x, h);
        }
        close free_listp(cls, fl, start, i);
    }
  }

  lemma void points_to_alloc_head_non_in_fl(list<dcell> cls, list<int> fl,
                                            int start, int x, int ahead)
  requires free_listp(cls, fl, start, start) &*&
           false == mem(ahead, fl) &*& nth(x,cls) == dcell(?p,ahead) &*&
           ahead != start;
  ensures free_listp(cls, fl, start, start) &*&
          false == mem(x, fl);
  {
    if (mem(x, fl)) {
      next_fl_member(cls, fl, start, x, start);
    }
  }
  @*/

/*@
  lemma void alloc_list_prev_next_mem(list<dcell> cls, list<int> al, int start,
                                      int x, int i)
  requires alloc_listp(cls, al, start, i) &*& true == mem(x, al) &*&
           nth(x, cls) == dcell(?p,?n);
  ensures alloc_listp(cls, al, start, i) &*&
          (mem(p, al) ? true : i == p) &*&
          (mem(n, al) ? true : n == start);
  {
    switch(al) {
      case nil: break;
      case cons(h,t):
        open alloc_listp(cls, al, start, i);
        if (h == x) {
          assert p == i;
          open alloc_listp(cls, t, start, h);
          switch(t) {
            case nil: break;
            case cons(th,tt):
          }
          close alloc_listp(cls, t, start, h);
        } else {
          alloc_list_prev_next_mem(cls, t, start, x, h);
          if (mem(p, t)) {
          } else {
          }
        }
        close alloc_listp(cls, al, start, i);
        break;
    }
  }
  @*/

/*@
lemma void add_to_free_list(list<dcell> cls, list<int> fl, int start, int x)
requires free_listp(cls, fl, start, start) &*& x != start &*&
         false == mem(x, fl) &*&
         false == mem(start, fl) &*&
         nth(start, cls) == dcell(_,?n) &*&
         0 <= x &*& x < length(cls) &*&
         0 <= start &*& start < length(cls);
ensures free_listp(update(start, dcell(x,x), update(x, dcell(n,n), cls)),
                   cons(x, fl), start, start);
{
  open free_listp(cls, fl, start, start);
  switch(fl) {
    case nil:
    case cons(h,t):
      free_list_update_unrelevant(cls, t, start, h, x, dcell(n,n));
      free_list_update_unrelevant(update(x, dcell(n,n), cls), t, start, h,
                                  start, dcell(x,x));
  }
  close free_listp(update(start, dcell(x,x), update(x, dcell(n,n), cls)),
                   fl, start, x);
  close free_listp(update(start, dcell(x,x), update(x, dcell(n,n), cls)),
                   cons(x, fl), start, start);
}
@*/

/*@
lemma void move_cell_to_free_engaged(list<int> al, list<int> fl,
                                     int el, nat size)
requires true == all_engaged(al, fl, size) &*&
         true == mem(el, al) &*&
         false == mem(el, remove(el, al));
ensures true == all_engaged(remove(el, al), cons(el,fl), size);
{
  switch(size) {
    case zero: return;
    case succ(n):
      move_cell_to_free_engaged(al, fl, el, n);
      if (int_of_nat(n) + INDEX_SHIFT == el) {
        assert true == mem(int_of_nat(n) + INDEX_SHIFT, cons(el,fl));
        assert false == mem(int_of_nat(n) + INDEX_SHIFT, remove(el, al));
      } else {
        neq_mem_remove(int_of_nat(n) + INDEX_SHIFT, el, al);
      }
  }
}
@*/

/*@
lemma void alloc_cell_points_back(list<dcell> cls, list<int> al,
                                  int start, int i, int x)
requires alloc_listp(cls, al, start, i) &*&
         true == mem(x, al) &*&
         nth(x, cls) == dcell(?p, ?n) &*&
         nth(p, cls) == dcell(?pp, ?pn) &*&
         nth(n, cls) == dcell(?np, ?nn);
ensures alloc_listp(cls, al, start, i) &*&
        pn == x &*& np == x;
{
  open alloc_listp(cls, al, start, i);
  switch(al) {
    case nil: break;
    case cons(h,t):
      if (h == x) {
        assert i == p;
        assert pn == x;
        open alloc_listp(cls, t, start, h);
        assert np == x;
        close alloc_listp(cls, t, start, h);
      } else {
        alloc_cell_points_back(cls, t, start, h, x);
      }
  }
  close alloc_listp(cls, al, start, i);
}

lemma void alloc_list_has_just_one_el(list<dcell> cls, list<int> al,
                                      int start, int x)
requires alloc_listp(cls, al, start, start) &*&
         false == mem(start, al) &*&
         true == mem(x, al) &*&
         nth(x, cls) == dcell(start,start);
ensures alloc_listp(cls, al, start, start) &*&
        al == cons(x,nil) &*&
        nth(start, cls) == dcell(x,x);
{
  alloc_cell_points_back(cls, al, start, start, x);
  assert nth(start, cls) == dcell(x,x);
  assert start != x;
  open alloc_listp(cls, al, start, start);
  switch(al) {
    case nil: break;
    case cons(h,t):
      assert h == x;
      open alloc_listp(cls, t, start, h);
      switch(t) {
        case nil: break;
        case cons(th,tt):
      }       
      close alloc_listp(cls, t, start, h);
  }
  close alloc_listp(cls, al, start, start);
}
@*/

/*@
  lemma void shift_inds_remove(list<int> al, int i, list<int> allocd)
  requires al == shift_inds_fp(allocd, INDEX_SHIFT);
  ensures remove(i, al) ==
          shift_inds_fp(remove(i-INDEX_SHIFT, allocd), INDEX_SHIFT);
  {
    switch(al){
      case nil:
        switch(allocd) {
          case nil: return;
          case cons(x,y):
            return;
        }
      case cons(h,t):
        switch(allocd) {
          case nil: return;
          case cons(all_h, all_t):
            shift_inds_remove(t, i, all_t);
        }
    }
  }
  @*/

/*@
  lemma void alloc_list_update_unrelevant_next(list<dcell> cls, list<int> al,
                                               int start, int ind, int next,
                                               int i)
  requires alloc_listp(cls, al, start, i) &*&
           0 <= start &*& start < length(cls) &*&
           ind != i &*&
           false == mem(ind, al) &*&
           nth(ind, cls) == dcell(?p, _);
  ensures alloc_listp(update(ind, dcell(p, next), cls), al, start, i);
  {
    open alloc_listp(cls, al, start, i);
    switch(al) {
      case nil:
        if (start == ind)
          nth_update(start, ind, dcell(p, next), cls);
        else
          nth_update_unrelevant(start, ind, dcell(p, next), cls);
        break;
      case cons(h,t):
        alloc_list_update_unrelevant_next(cls, t, start, ind, next, h);
        nth_update_unrelevant(h, ind, dcell(p, next), cls);
    }
    nth_update_unrelevant(i, ind, dcell(p, next), cls);
    close alloc_listp(update(ind, dcell(p, next), cls), al, start, i);
  }
  @*/

/*@
lemma void alloc_list_remove_iter(list<dcell> cls, list<int> al, int start,
                                  int x, int i)
requires alloc_listp(cls, al, start, i) &*& true == mem(x, al) &*&
         false == mem(i, al) &*&
         false == mem(start, al) &*&
         x != start &*&
         x != i &*&
         nth(x, cls) == dcell(?p, ?n) &*&
         nth(p, cls) == dcell(?pp, x) &*&
         nth(n, cls) == dcell(x, ?nn) &*&
         0 <= p &*& p < length(cls) &*&
         0 <= n &*& n < length(cls) &*&
         0 <= start &*& start < length(cls) &*&
         p != n;
ensures alloc_listp(update(n, dcell(p, nn),
                     update(p, dcell(pp, n), cls)),
                    remove(x, al), start, i);
{
  switch(al) {
    case nil: return;
    case cons(h,t):
      alloc_list_no_dups_head(cls, al, start, i);
      open alloc_listp(cls, al, start, i);
      if (h == x) {
        assert i == p;
        switch(t) {
          case nil:
            open alloc_listp(cls, t, start, h);
            assert remove(x, al) == nil;
            assert n == start;
            break;
          case cons(th,tt):
            alloc_list_no_dups_head(cls, t, start, h);
            open alloc_listp(cls, t, start, h);
            assert th == n;
            open alloc_listp(cls, tt, start, th);
            switch(tt) {
              case nil:
                nth_update(start, p, dcell(pp, n), cls);
                nth_update_unrelevant(start, n, dcell(p, nn),
                                      update(p, dcell(pp, n), cls));
                close alloc_listp(update(n, dcell(p, nn),
                                   update(p, dcell(pp, n), cls)),
                                  nil, start, th);
                break;
              case cons(tth,ttt):
                alloc_list_update_unrelevant_next(cls,
                                                  ttt, start,
                                                  p, n,
                                                  tth);
                alloc_list_update_unrelevant(update(p, dcell(pp, n), cls),
                                             ttt, start,
                                             n, dcell(p, nn),
                                             tth);
                assert alloc_listp(update(n, dcell(p, nn),
                                    update(p, dcell(pp, n), cls)),
                                   ttt, start, tth);
                nth_update_unrelevant(tth, p, dcell(pp, n), cls);
                nth_update_unrelevant(tth, n, dcell(p, nn),
                                      update(p, dcell(pp, n), cls));
                close alloc_listp(update(n, dcell(p, nn),
                                   update(p, dcell(pp, n), cls)),
                                  tt, start, th);
            }
        }
        assert remove(x, al) == t;
        nth_update(p, p, dcell(pp, n), cls);
        nth_update(n, n, dcell(p, nn), update(p, dcell(pp, n), cls));
        nth_update_unrelevant(p, n, dcell(p, nn), update(p, dcell(pp, n), cls));
        close alloc_listp(update(n, dcell(p, nn),
                           update(p, dcell(pp, n), cls)),
                          t, start, i);
      } else {
        alloc_list_remove_iter(cls, t, start, x, h);
        if (i == n) {
          assert i != p;
          nth_update(i, n, dcell(p, nn), update(p, dcell(pp, n), cls));
        } else {
          if (i == p) {
            assert h == x;
          } else {
            nth_update_unrelevant(i, p, dcell(pp, n), cls);
          }
          nth_update_unrelevant(i, n, dcell(p, nn), update(p, dcell(pp, n), cls));
        }
        if (h == n) {
          assert i == x;
        } else {
          if (h == p) {
            nth_update(h, p, dcell(pp, n), cls);
          } else {
            nth_update_unrelevant(h, p, dcell(pp, n), cls);
          }
          nth_update_unrelevant(h, n, dcell(p, nn), update(p, dcell(pp, n), cls));
        }
        close alloc_listp(update(n, dcell(p, nn),
                           update(p, dcell(pp, n), cls)),
                          remove(x, al), start, i);
      }

  }
}

lemma void alloc_list_remove(list<dcell> cls, list<int> al, int start, int x)
requires alloc_listp(cls, al, start, start) &*& true == mem(x, al) &*&
         false == mem(start, al) &*&
         x != start &*&
         nth(x, cls) == dcell(?p, ?n) &*&
         nth(p, cls) == dcell(?pp, _) &*&
         nth(n, cls) == dcell(_, ?nn) &*&
         0 <= p &*& p < length(cls) &*&
         0 <= n &*& n < length(cls) &*&
         0 <= start &*& start < length(cls) &*&
         p != n;
ensures alloc_listp(update(n, dcell(p, nn),
                     update(p, dcell(pp, n), cls)),
                    remove(x, al), start, start);
{
  alloc_cell_points_back(cls, al, start, start, x);
  alloc_list_remove_iter(cls, al, start, x, start);
}
@*/

int dchain_impl_free_index(struct dchain_cell *cells, int index)
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_fp(dc, index) ?
             (dchainip(dchaini_remove_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/
{
  //@ open dchainip(dc, cells);
  //@ int size = dchaini_irange_fp(dc);
  //@ assert dcellsp(cells, ?clen, ?cls);
  //@ assert free_listp(cls, ?fl, FREE_LIST_HEAD, FREE_LIST_HEAD);
  //@ assert alloc_listp(cls, ?al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ dcellsp_length(cells);
  //@ dcells_limits(cells);
  //@ extract_heads(cells, cls);
  int freed = index + INDEX_SHIFT;
  //@ extract_cell(cells, cls, freed);
  struct dchain_cell* freedp = cells + freed;
  int freed_prev = freedp->prev;
  int freed_next = freedp->next;
  //@ glue_cells(cells, cls, freed);
  /* The index is already free. */
  if (freed_next == freed_prev) {
    if (freed_prev != ALLOC_LIST_HEAD) {
      //@ lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
      //@ symm_non_alloc(cls, al, ALLOC_LIST_HEAD, freed);
      //@ assert false == mem(freed, al);
      //@ shift_inds_mem(dchaini_alist_fp(dc), INDEX_SHIFT, freed);
      //@ assert false == mem(index, dchaini_alist_fp(dc));
      //@ attach_heads(cells, cls);
      //@ close dchainip(dc, cells);
      return 0;
    } else {
      //@ lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      /*@ points_to_alloc_head_non_in_fl(cls, fl, FREE_LIST_HEAD,
                                         freed, ALLOC_LIST_HEAD); @*/
    }
  } else {
    /*@ asymm_non_in_free_list(cls, fl, FREE_LIST_HEAD, freed,
                               FREE_LIST_HEAD); @*/
  }

  //@ mul_nonnegative(size, sizeof(struct dchain_cell));
  struct dchain_cell* fr_head = cells + FREE_LIST_HEAD;

  //@ assert false == mem(freed, fl);
  //@ free_alloc_disjoint(al, fl, freed, nat_of_int(size));
  //@ assert true == mem(freed, al);
  //@ alloc_list_prev_next_mem(cls, al, ALLOC_LIST_HEAD, freed, ALLOC_LIST_HEAD);
  /*@
    if (freed_prev == freed_next) {
      assert freed_prev == ALLOC_LIST_HEAD;
      assert freed_next == ALLOC_LIST_HEAD;
      lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
      alloc_list_has_just_one_el(cls, al, ALLOC_LIST_HEAD, freed);
      assert nth(0,cls) == dcell(freed, freed);
      assert al == cons(freed, nil);
    } else {
      forall_nth(cls, (dbounded)(size+INDEX_SHIFT), freed);
      dcells_limits(cells+INDEX_SHIFT);
      if (freed_prev == ALLOC_LIST_HEAD) {
      } else {
        forall_mem(freed_prev, al, (lbounded)(INDEX_SHIFT));
        extract_cell(cells, cls, freed_prev);
      }
    }
  @*/

  /* Extract the link from the "alloc" chain. */
  //@ mul_nonnegative(freed_prev, sizeof(struct dchain_cell));
  struct dchain_cell* freed_prevp = cells + freed_prev;
  freed_prevp->next = freed_next;

  //@ list<dcell> ncls1;

  /*@
    if (freed_prev != freed_next) {
      dcell nfpr = dcell(dchain_cell_get_prev(nth(freed_prev, cls)),freed_next);
      ncls1 = update(freed_prev, nfpr, cls);
      if (freed_prev == ALLOC_LIST_HEAD) {
        drop_update_unrelevant(INDEX_SHIFT, freed_prev, nfpr, cls);
      } else {
        drop_update_relevant(INDEX_SHIFT, freed_prev, nfpr, cls);
        take_update_unrelevant(freed_prev-INDEX_SHIFT,
                              freed_prev-INDEX_SHIFT, nfpr,
                              drop(INDEX_SHIFT, cls));
        drop_update_unrelevant(freed_prev+1, freed_prev, nfpr, cls);
        glue_cells(cells, ncls1, freed_prev);
      }
      if (freed_next == ALLOC_LIST_HEAD) {
      } else {
        forall_mem(freed_next, al, (lbounded)(INDEX_SHIFT));
        extract_cell(cells, ncls1, freed_next);
      }
    } else {
      ncls1 = cls;
    }
    @*/

  struct dchain_cell* freed_nextp = cells + freed_next;
  freed_nextp->prev = freed_prev;

  //@ list<dcell> ncls2;

  /*@
    if (freed_prev != freed_next) {
      dcell nfne = dcell(freed_prev,dchain_cell_get_next(nth(freed_next, cls)));
      ncls2 = update(freed_next, nfne, ncls1);
      if (freed_next == ALLOC_LIST_HEAD) {
        drop_update_unrelevant(INDEX_SHIFT, freed_next, nfne, ncls1);
      } else {
        drop_update_relevant(INDEX_SHIFT, freed_next, nfne, ncls1);
        take_update_unrelevant(freed_next-INDEX_SHIFT,
                               freed_next-INDEX_SHIFT, nfne,
                               drop(INDEX_SHIFT, ncls1));
        drop_update_unrelevant(freed_next+1, freed_next, nfne, ncls1);
        glue_cells(cells, ncls2, freed_next);
      }
    } else {
      dcell nalh = dcell(ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
      ncls2 = update(ALLOC_LIST_HEAD, nalh, ncls1);
      drop_update_unrelevant(INDEX_SHIFT, ALLOC_LIST_HEAD, nalh, ncls1);
    }
    @*/
  //@ extract_cell(cells, ncls2, freed);

  /* Add the link to the "free" chain. */
  freedp->next = fr_head->next;
  freedp->prev = freedp->next;
  //@ int fr_fst = dchain_cell_get_next(nth(FREE_LIST_HEAD, cls));
  //@ dcell nfreed = dcell(fr_fst, fr_fst);
  //@ list<dcell> ncls3 = update(freed, nfreed, ncls2);
  //@ drop_update_relevant(INDEX_SHIFT, freed, nfreed, ncls2);
  /*@ take_update_unrelevant(freed-INDEX_SHIFT, freed-INDEX_SHIFT,
                             nfreed, drop(INDEX_SHIFT, ncls2)); @*/
  //@ drop_update_unrelevant(freed+1, freed, nfreed, ncls2);

  //@ glue_cells(cells, ncls3, freed);

  fr_head->next = freed;
  fr_head->prev = fr_head->next;
  //@ list<dcell> ncls4 = update(FREE_LIST_HEAD, dcell(freed, freed), ncls3);
  //@ drop_update_unrelevant(INDEX_SHIFT, FREE_LIST_HEAD, dcell(freed, freed), ncls3);
  //@ attach_heads(cells, ncls4);
  //@ lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
  //@ alloc_list_no_dups_head(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  /*@
    if (freed_prev == freed_next) {
    // update(1, dcell(freed,freed), update(freed, nfreed, update(0, nalh, cls)));

      close alloc_listp(ncls2, nil, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
      alloc_list_update_unrelevant(ncls2, nil, ALLOC_LIST_HEAD,
                                   freed, nfreed,
                                   ALLOC_LIST_HEAD);
      alloc_list_update_unrelevant(ncls3, nil, ALLOC_LIST_HEAD,
                                   FREE_LIST_HEAD, dcell(freed, freed),
                                   ALLOC_LIST_HEAD);

      free_list_update_unrelevant(cls, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  ALLOC_LIST_HEAD,
                                  dcell(ALLOC_LIST_HEAD, ALLOC_LIST_HEAD));
      lbounded_then_start_nonmem(fl, FREE_LIST_HEAD);
      add_to_free_list(ncls2, fl, FREE_LIST_HEAD, freed);

      dcell nalh = dcell(ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
      forall_nth(cls, (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD);
      forall_update(cls, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD, nalh);
      forall_update(update(ALLOC_LIST_HEAD, nalh, cls),
                    (dbounded)(size+INDEX_SHIFT), freed, nfreed);
      forall_update(update(freed, nfreed,
                     update(ALLOC_LIST_HEAD, nalh, cls)),
                    (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD,
                    dcell(freed,freed));
      assert nil == remove(freed, al);
      open alloc_listp(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
      open alloc_listp(cls, nil, ALLOC_LIST_HEAD, freed);
    } else {
      // update(1, dcell(freed, freed),
      //  update(freed, nfreed,
      //   update(freed_next, nfne,
      //    update(freed_prev, nfpr, cls))))
      dcell nfne = dcell(freed_prev,dchain_cell_get_next(nth(freed_next, cls)));
      dcell nfpr = dcell(dchain_cell_get_prev(nth(freed_prev, cls)),freed_next);
      forall_nth(cls, (dbounded)(size+INDEX_SHIFT), freed);
      forall_nth(cls, (dbounded)(size+INDEX_SHIFT), freed_prev);
      forall_nth(cls, (dbounded)(size+INDEX_SHIFT), freed_next);
      forall_nth(cls, (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD);
      forall_update(cls, (dbounded)(size+INDEX_SHIFT), freed_prev, nfpr);
      forall_update(ncls1, (dbounded)(size+INDEX_SHIFT), freed_next, nfne);
      forall_update(ncls2, (dbounded)(size+INDEX_SHIFT), freed, nfreed);
      forall_update(ncls3, (dbounded)(size+INDEX_SHIFT), FREE_LIST_HEAD,
                    dcell(freed, freed));

      alloc_list_no_dups(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD, freed);
      lbounded_then_start_nonmem(al, FREE_LIST_HEAD);
      neq_mem_remove(FREE_LIST_HEAD, freed, al);
      alloc_list_remove(cls, al, ALLOC_LIST_HEAD, freed);
      alloc_list_update_unrelevant(ncls2, remove(freed, al),
                                   ALLOC_LIST_HEAD,
                                   freed, nfreed,
                                   ALLOC_LIST_HEAD);
      alloc_list_update_unrelevant(ncls3, remove(freed, al),
                                   ALLOC_LIST_HEAD,
                                   FREE_LIST_HEAD, dcell(freed, freed),
                                   ALLOC_LIST_HEAD);

      assert true == mem(freed, al);
      free_alloc_disjoint(al, fl, freed, nat_of_int(size));
      assert false == mem(freed, fl);
      if (freed_prev == ALLOC_LIST_HEAD) {
        lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      } else {
        assert true == mem(freed_prev, al);
        free_alloc_disjoint(al, fl, freed_prev, nat_of_int(size));
        assert false == mem(freed_prev, fl);
      }
      if (freed_next == ALLOC_LIST_HEAD) {
        lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      } else {
        assert true == mem(freed_next, al);
        free_alloc_disjoint(al, fl, freed_next, nat_of_int(size));
        assert false == mem(freed_next, fl);
      }
      free_list_update_unrelevant(cls, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  freed_prev, nfpr);
      free_list_update_unrelevant(ncls1, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  freed_next, nfne);
      lbounded_then_start_nonmem(fl, FREE_LIST_HEAD);
      add_to_free_list(ncls2, fl, FREE_LIST_HEAD, freed);
    }
    @*/
  //@ shift_inds_mem(dchaini_alist_fp(dc), INDEX_SHIFT, freed);
  //@ move_cell_to_free_engaged(al, fl, freed, nat_of_int(size));
  //@ forall_remove(al, freed, (lbounded)(INDEX_SHIFT));
  //@ shift_inds_remove(al, freed, dchaini_alist_fp(dc));
  //@ close dchainip(dchaini_remove_fp(dc, index), cells);
  return 1;
}

/*@
  lemma void alloc_list_empty(list<dcell> cls, list<int> al, int start)
  requires alloc_listp(cls, al, start, start) &*&
           nth(start, cls) == dcell(start, start);
  ensures alloc_listp(cls, al, start, start) &*&
          al == nil;
  {
    switch(al) {
      case nil: return;
      case cons(h,t):
        open alloc_listp(cls, al, start, start);
        close alloc_listp(cls, al, start, start);
    }
  }

  lemma void shift_inds_empty(list<int> x, int shift)
  requires nil == shift_inds_fp(x, shift);
  ensures x == nil;
  {
    switch(x) {
      case nil: return;
      case cons(h,t):
        assert shift_inds_fp(x, shift) ==
               cons(h - shift, shift_inds_fp(t, shift));
        return;
    }
  }
  @*/

int dchain_impl_get_oldest_index(struct dchain_cell *cells, int *index)
/*@ requires dchainip(?dc, cells) &*& *index |-> ?i; @*/
/*@ ensures dchainip(dc, cells) &*&
            (dchaini_is_empty_fp(dc) ?
             (*index |-> i &*&
              result == 0) :
             (*index |-> ?oi &*&
              oi == dchaini_get_oldest_index_fp(dc) &*&
              0 <= oi &*& oi < dchaini_irange_fp(dc) &*&
              true == dchaini_allocated_fp(dc, oi) &*&
              result == 1)); @*/
{
  //@ open dchainip(dc, cells);
  //@ int size = dchaini_irange_fp(dc);
  //@ assert dcellsp(cells, ?clen, ?cls);
  //@ assert alloc_listp(cls, ?al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ dcellsp_length(cells);
  //@ dcells_limits(cells);
  //@ extract_heads(cells, cls);
  struct dchain_cell *al_head = cells + ALLOC_LIST_HEAD;
  /* No allocated indexes. */
  if (al_head->next == al_head->prev) {
    if (al_head->next == ALLOC_LIST_HEAD) {
      //@ alloc_list_empty(cls, al, ALLOC_LIST_HEAD);
      //@ assert al == nil;
      //@ shift_inds_empty(dchaini_alist_fp(dc), INDEX_SHIFT);
      //@ attach_heads(cells, cls);
      //@ close dchainip(dc, cells);
      return 0;
    }
  }
  //@ open alloc_listp(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ assert al == cons(?oldest, _);
  //@ assert oldest == al_head->next;
  //@ close alloc_listp(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  *index = al_head->next - INDEX_SHIFT;
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD);
  //@ forall_mem(oldest, al, (lbounded)(INDEX_SHIFT));
  //@ assert *index |-> ?oi;
  //@ assert oi < dchaini_irange_fp(dc);
  //@ assert dchaini_alist_fp(dc) == cons(oldest - INDEX_SHIFT, _);
  //@ attach_heads(cells, cls);
  //@ close dchainip(dc, cells);
  return 1;
}

/*@
  lemma void shift_inds_single_element(list<int> lst, int shift)
  requires shift_inds_fp(lst, shift) == cons(?x, nil);
  ensures lst == cons(x - shift, nil);
  {
    switch(lst) {
      case nil:
        return;
      case cons(h,t):
        shift_inds_empty(t, shift);
    }
  }
  @*/

/*@
  lemma void rejuvenate_still_all_engaged(list<int> al, list<int> fl,
                                          int x, nat size)
  requires true == all_engaged(al, fl, size) &*&
           false == mem(x, fl);
  ensures true == all_engaged(append(remove(x, al), cons(x, nil)), fl, size);
  {
    switch(size) {
      case zero: return;
      case succ(n):
        rejuvenate_still_all_engaged(al, fl, x, n);
        if (int_of_nat(n) + INDEX_SHIFT == x) {
          assert true == mem(int_of_nat(n) + INDEX_SHIFT,
                             append(remove(x, al), cons(x, nil)));
          assert false == mem(int_of_nat(n) + INDEX_SHIFT, fl);
        } else {
          neq_mem_remove(int_of_nat(n) + INDEX_SHIFT, x, al);
          mem_append(int_of_nat(n) + INDEX_SHIFT,
                     remove(x, al), cons(x, nil));
        }
    }
  }
  @*/

int dchain_impl_rejuvenate_index(struct dchain_cell *cells, int index)
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_fp(dc, index) ?
             (dchainip(dchaini_rejuvenate_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/
{
  //@ open dchainip(dc, cells);
  //@ int size = dchaini_irange_fp(dc);
  //@ assert dcellsp(cells, ?clen, ?cls);
  //@ assert free_listp(cls, ?fl, FREE_LIST_HEAD, FREE_LIST_HEAD);
  //@ assert alloc_listp(cls, ?al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ dcellsp_length(cells);
  //@ dcells_limits(cells);
  //@ extract_heads(cells, cls);
  int lifted = index + INDEX_SHIFT;
  //@ extract_cell(cells, cls, lifted);
  struct dchain_cell *liftedp = cells + lifted;
  int lifted_next = liftedp->next;
  int lifted_prev = liftedp->prev;
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), lifted);
  //@ glue_cells(cells, cls, lifted);
  /* The index is not allocated. */
  if (lifted_next == lifted_prev) {
    if (lifted_next != ALLOC_LIST_HEAD) {
      //@ lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
      //@ symm_non_alloc(cls, al, ALLOC_LIST_HEAD, lifted);
      //@ assert false == mem(lifted, al);
      //@ shift_inds_mem(dchaini_alist_fp(dc), INDEX_SHIFT, lifted);
      //@ assert false == mem(index, dchaini_alist_fp(dc));
      //@ attach_heads(cells, cls);
      //@ close dchainip(dc, cells);
      return 0;
    } else {
      /* There is only one element allocated - no point in changing anything */
      //@ assert lifted_prev == ALLOC_LIST_HEAD;
      //@ assert lifted_next == ALLOC_LIST_HEAD;
      //@ lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      /*@ points_to_alloc_head_non_in_fl(cls, fl, FREE_LIST_HEAD,
                                         lifted, ALLOC_LIST_HEAD); @*/
      //@ free_alloc_disjoint(al, fl, lifted, nat_of_int(size));
      //@ assert true == mem(lifted, al);
      //@ lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
      //@ alloc_list_has_just_one_el(cls, al, ALLOC_LIST_HEAD, lifted);
      //@ assert nth(0,cls) == dcell(lifted, lifted);
      //@ assert al == cons(lifted, nil);
      //@ shift_inds_single_element(dchaini_alist_fp(dc), INDEX_SHIFT);
      //@ assert dchaini_alist_fp(dc) == cons(index, nil);

      //@ attach_heads(cells, cls);
      //@ close dchainip(dc, cells);
      return 1;
    }
  } else {
    /*@ asymm_non_in_free_list(cls, fl, FREE_LIST_HEAD, lifted,
                               FREE_LIST_HEAD); @*/
    //@ free_alloc_disjoint(al, fl, lifted, nat_of_int(size));
    //@ assert true == mem(lifted, al);
    //@ alloc_list_prev_next_mem(cls, al, ALLOC_LIST_HEAD, lifted, ALLOC_LIST_HEAD);
    /*@
    if (lifted_next == ALLOC_LIST_HEAD) {
      lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      assert lifted_prev != ALLOC_LIST_HEAD;
      assert true == mem(lifted_prev, al);
      forall_mem(lifted_prev, al, (lbounded)(INDEX_SHIFT));
      free_alloc_disjoint(al, fl, lifted_prev, nat_of_int(size));
    } else {
      assert lifted_next != ALLOC_LIST_HEAD;
      assert true == mem(lifted_next, al);
      forall_mem(lifted_next, al, (lbounded)(INDEX_SHIFT));
      if (lifted_prev == ALLOC_LIST_HEAD) {
        lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      } else {
        assert true == mem(lifted_prev, al);
        forall_mem(lifted_prev, al, (lbounded)(INDEX_SHIFT));
        free_alloc_disjoint(al, fl, lifted_prev, nat_of_int(size));
      }
      free_alloc_disjoint(al, fl, lifted_next, nat_of_int(size));
    }
    @*/
  }

  //@ assert false == mem(lifted_prev, fl);
  //@ assert false == mem(lifted_next, fl);
  /* Unlink it from the middle of the "alloc" chain. */
  /*@
    if (lifted_prev != ALLOC_LIST_HEAD) {
      dcells_limits(cells+INDEX_SHIFT);
      extract_cell(cells, cls, lifted_prev);
    }
    @*/
  struct dchain_cell *lifted_prevp = cells + lifted_prev;
  lifted_prevp->next = lifted_next;

  //@ dcell nlifted_prev = dcell(dchain_cell_get_prev(nth(lifted_prev, cls)), lifted_next);
  //@ list<dcell> ncls1 = update(lifted_prev, nlifted_prev, cls);
  /*@
    if (lifted_prev != ALLOC_LIST_HEAD) {
      drop_update_relevant(INDEX_SHIFT, lifted_prev, nlifted_prev, cls);
      take_update_unrelevant(lifted_prev-INDEX_SHIFT, lifted_prev-INDEX_SHIFT,
                             nlifted_prev, drop(INDEX_SHIFT, cls));
      drop_update_unrelevant(lifted_prev+1, lifted_prev, nlifted_prev, cls);
      glue_cells(cells, ncls1, lifted_prev);
    } else {
      drop_update_unrelevant(INDEX_SHIFT, lifted_prev, nlifted_prev, cls);
    }
    @*/
  /*@
    if (lifted_next != ALLOC_LIST_HEAD) {
      dcells_limits(cells+INDEX_SHIFT);
      extract_cell(cells, ncls1, lifted_next);
    }
    @*/

  struct dchain_cell *lifted_nextp = cells + lifted_next;
  lifted_nextp->prev = lifted_prev;

  //@ dcell nlifted_next = dcell(lifted_prev, dchain_cell_get_next(nth(lifted_next, cls)));
  //@ list<dcell> ncls2 = update(lifted_next, nlifted_next, ncls1);
  /*@
    if (lifted_next != ALLOC_LIST_HEAD) {
      drop_update_relevant(INDEX_SHIFT, lifted_next, nlifted_next, ncls1);
      take_update_unrelevant(lifted_next-INDEX_SHIFT, lifted_next-INDEX_SHIFT,
                             nlifted_next, drop(INDEX_SHIFT, ncls1));
      drop_update_unrelevant(lifted_next+1, lifted_next, nlifted_next, ncls1);
      glue_cells(cells, ncls2, lifted_next);
    } else {
      drop_update_unrelevant(INDEX_SHIFT, lifted_next, nlifted_next, ncls1);
    }
    @*/

  struct dchain_cell *al_head = cells + ALLOC_LIST_HEAD;
  int al_head_prev = al_head->prev;

  //@ extract_cell(cells, ncls2, lifted);

  /* Link it at the very end - right before the special link. */
  liftedp->next = ALLOC_LIST_HEAD;
  liftedp->prev = al_head_prev;

  //@ lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
  //@ last_alloc_list_mem(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ alloc_list_no_dups(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD, lifted);
  //@ neq_mem_remove(FREE_LIST_HEAD, lifted, al);
  //@ alloc_list_remove(cls, al, ALLOC_LIST_HEAD, lifted);

  //@ open alloc_listp(ncls2, remove(lifted, al), ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ assert remove(lifted, al) == cons(?oldest, _);
  //@ close alloc_listp(ncls2, remove(lifted, al), ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);

  //@ last_alloc_list_mem(ncls2, remove(lifted, al), ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ assert true == mem(al_head_prev, remove(lifted, al));
  //@ dcell nlifted = dcell(al_head_prev, ALLOC_LIST_HEAD);
  //@ list<dcell> ncls3 = update(lifted, nlifted, ncls2);
  //@ drop_update_relevant(INDEX_SHIFT, lifted, nlifted, ncls2);
  /*@ take_update_unrelevant(lifted-INDEX_SHIFT, lifted-INDEX_SHIFT,
                             nlifted, drop(INDEX_SHIFT, ncls2));
                         @*/
  //@ drop_update_unrelevant(lifted+1, lifted, nlifted, ncls2);
  //@ glue_cells(cells, ncls3, lifted);

  //@ forall_remove(al, lifted, (lbounded)(INDEX_SHIFT));
  //@ forall_mem(al_head_prev, remove(lifted, al), (lbounded)(INDEX_SHIFT));
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), lifted);
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), lifted_prev);
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), lifted_next);
  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD);
  //@ forall_update(cls, (dbounded)(size+INDEX_SHIFT), lifted_prev, nlifted_prev);
  //@ forall_update(ncls1, (dbounded)(size+INDEX_SHIFT), lifted_next, nlifted_next);
  //@ forall_update(ncls2, (dbounded)(size+INDEX_SHIFT), lifted, nlifted);
  //@ forall_nth(ncls3, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD);
  //@ extract_cell(cells, ncls3, al_head_prev);

  //@ forall_nth(cls, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD);
  //@ mul_nonnegative(al_head_prev, sizeof(struct dchain_cell));
  struct dchain_cell *al_head_prevp = cells + al_head_prev;
  al_head_prevp->next = lifted;
  //@ list<dcell> ncls4;
  //@ dcell nal_head_prev = dcell(dchain_cell_get_prev(nth(al_head_prev, ncls2)), lifted);
  //@ ncls4 = update(al_head_prev, nal_head_prev, ncls3);
  //@ drop_update_relevant(INDEX_SHIFT, al_head_prev, nal_head_prev, ncls3);
  /*@ take_update_unrelevant(al_head_prev-INDEX_SHIFT, al_head_prev-INDEX_SHIFT,
                             nal_head_prev, drop(INDEX_SHIFT, ncls3));
                             @*/
  //@ drop_update_unrelevant(al_head_prev+1, al_head_prev, nal_head_prev, ncls3);
  //@ glue_cells(cells, ncls4, al_head_prev);
  al_head->prev = lifted;
  //@ dcell nal_head = dcell(lifted, dchain_cell_get_next(nth(ALLOC_LIST_HEAD, ncls2)));
  //@ list<dcell> ncls5 = update(ALLOC_LIST_HEAD, nal_head, ncls4);
  //@ drop_update_unrelevant(INDEX_SHIFT, ALLOC_LIST_HEAD, nal_head, ncls4);
  //@ attach_heads(cells, ncls5);
  //@ forall_nth(ncls2, (dbounded)(size+INDEX_SHIFT), al_head_prev);
  //@ forall_update(ncls3, (dbounded)(size+INDEX_SHIFT), al_head_prev, nal_head_prev);
  //@ forall_update(ncls4, (dbounded)(size+INDEX_SHIFT), ALLOC_LIST_HEAD, nal_head);
  //@ lbounded_then_start_nonmem(remove(lifted, al), ALLOC_LIST_HEAD);
  //@ assert alloc_listp(ncls2, remove(lifted, al), ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
  //@ insert_alloc_list(ncls2, remove(lifted, al), ALLOC_LIST_HEAD, lifted);
  //@ update_update(ncls2, al_head_prev, nal_head_prev, lifted, nlifted);
  //@ assert alloc_listp(ncls5, append(remove(lifted, al), cons(lifted, nil)), 0, 0);
  /*@
    {
      assert true == mem(al_head_prev, remove(lifted, al));
      free_alloc_disjoint(al, fl, al_head_prev, nat_of_int(size));
      lbounded_then_start_nonmem(fl, ALLOC_LIST_HEAD);
      free_list_update_unrelevant(cls, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  lifted_prev, nlifted_prev);
      free_list_update_unrelevant(ncls1, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  lifted_next, nlifted_next);
      free_list_update_unrelevant(ncls2, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  lifted, nlifted);
      free_list_update_unrelevant(ncls3, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  al_head_prev, nal_head_prev);
      free_list_update_unrelevant(ncls4, fl, FREE_LIST_HEAD, FREE_LIST_HEAD,
                                  ALLOC_LIST_HEAD, nal_head);
    }
    @*/
  //@ forall_remove(al, lifted, (lbounded)(INDEX_SHIFT));
  //@ forall_append(remove(lifted, al), cons(lifted, nil), (lbounded)(INDEX_SHIFT));
  //@ rejuvenate_still_all_engaged(al, fl, lifted, nat_of_int(size));
  //@ list<int> alist = dchaini_alist_fp(dc);
  //@ shift_inds_remove(al, lifted, alist);
  //@ shift_inds_append(remove(lifted, al), lifted, remove(index, alist));
  //@ assert true == mem(lifted, al);
  //@ shift_inds_mem(dchaini_alist_fp(dc), INDEX_SHIFT, lifted);
  //@ close dchainip(dchaini_rejuvenate_fp(dc, index), cells);
  return 1;
}

/*@
lemma void dchaini_no_dups(struct dchain_cell *cells, dchaini dc, int index)
requires dchainip(dc, cells);
ensures dchainip(dc, cells) &*&
        false == dchaini_allocated_fp(dchaini_remove_fp(dc, index), index);
{
  open dchainip(dc, cells);
  assert dcellsp(cells, ?clen, ?cls);
  assert alloc_listp(cls, ?al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);

  switch(dc) { case dchaini(alist, size):
    lbounded_then_start_nonmem(al, ALLOC_LIST_HEAD);
    alloc_list_no_dups(cls, al, ALLOC_LIST_HEAD,
                       ALLOC_LIST_HEAD, index+INDEX_SHIFT);
    shift_inds_remove(al, index+INDEX_SHIFT, alist);
    shift_inds_mem(remove(index, alist), INDEX_SHIFT, index+INDEX_SHIFT);
  }

  close dchainip(dc, cells);
}
@*/

/*@
  lemma void dchaini_alist_upperbound(struct dchain_cell *cells, dchaini dc)
  requires dchainip(dc, cells);
  ensures dchainip(dc, cells) &*&
          length(dchaini_alist_fp(dc)) <= dchaini_irange_fp(dc);
  {
    open dchainip(dc, cells);
    assert dcellsp(cells, ?clen, ?cls);
    assert alloc_listp(cls, ?al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);

    switch(dc) { case dchaini(alist, size):
      assert length(al) <= size;
      shift_inds_len(alist, INDEX_SHIFT);
    }

    close dchainip(dc, cells);
  }
  @*/
