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
      case nil: return nth(cur, cells) == dcell(start,start);
      case cons(h,t):
        return nth(cur, cells) == dcell(h,h) &*&
               cur != h &*&
               free_listp(cells, t, start, h);
    };

  predicate alloc_listp(list<dcell> cells, list<int> alloc, int start, int cur) =
    switch(alloc) {
      case nil: return nth(cur, cells) == dcell(?x,start) &*&
                       nth(start, cells) == dcell(cur, ?y) &*&
                       cur == start ?
                         (x == start &*& y == cur) :
                         (x != start &*& y != cur);
      case cons(h,t):
        return nth(cur, cells) == dcell(?x, h) &*&
               nth(h, cells) == dcell(cur, ?y) &*&
               x != h &*& y != cur &*&
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
              (mem(int_of_nat(n) + INDEX_SHIFT, al) ||
               mem(int_of_nat(n) + INDEX_SHIFT, fl));
    }
  }

  predicate dchainip(dchaini ch,
                     struct dchain_cell * cells) =
    switch(ch) { case dchaini(allocd, size):
      return
        0 < size &*&
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
  requires dcellsp(cells+INDEX_SHIFT, length(cls)-2, drop(2,cls)) &*&
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


/*@
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

  lemma void all_engaged_and_this(list<int> al, list<int> fl, int x, nat size)
  requires true == all_engaged(al, fl, size) &*&
           0 <= x &*& x < int_of_nat(size);
  ensures mem(x+INDEX_SHIFT, fl) ? true : true == mem(x+INDEX_SHIFT, al);
  {
    switch(size) {
      case zero: return;
      case succ(n):
        if (x == int_of_nat(n)) {
        } else {
          all_engaged_and_this(al, fl, x, n);
        }
    }
  }

  lemma void free_alloc_disjoint(list<dcell> cls, list<int> al, list<int> fl,
                                 int x, nat size)
  requires free_listp(cls, fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*&
           alloc_listp(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD) &*&
           true == all_engaged(al, fl, size) &*&
           INDEX_SHIFT <= x &*& x < int_of_nat(size) + INDEX_SHIFT;
  ensures free_listp(cls, fl, FREE_LIST_HEAD, FREE_LIST_HEAD) &*&
          alloc_listp(cls, al, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD) &*&
          mem(x, fl) != mem(x, al);
  {
    if (mem(x, fl)) {
      free_mem_symm(cls, fl, x, FREE_LIST_HEAD, FREE_LIST_HEAD);
      if (mem(x, al)) {
        alloc_mem_asymm(cls, al, x, ALLOC_LIST_HEAD, ALLOC_LIST_HEAD);
      }
    } else {
      all_engaged_and_this(al, fl, x-INDEX_SHIFT, size);
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

  lemma void all_engaged_len_lb(list<int> al, list<int> fl, nat size)
  requires true == all_engaged(al, fl, size);
  ensures int_of_nat(size) <= length(al) + length(fl);
  {
    switch(size) {
      case zero:
        return;
      case succ(n):
        int x = int_of_nat(n)+INDEX_SHIFT;
        if (mem(x, fl)) {
          all_engaged_remove_unrelevant(al, fl, x, n);
          all_engaged_len_lb(al, remove(x, fl), n);
        } else {
          assume(false);
        }
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
                                     int start, int x)
  requires alloc_listp(cls, al, start, start) &*& nth(start, cls) == dcell(x,_);
  ensures alloc_listp(cls, al, start, start) &*& true == mem(x, al);
  {
    assume(false);
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
    //@ all_engaged_len_lb(al, fl, nat_of_int(size));
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
  // @ free_list_above_alloc(cls, fl, 1);
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
  /*@ if (al_head->prev != ALLOC_LIST_HEAD)
        if (al_head->prev != FREE_LIST_HEAD) {
          note(0 < al_head->prev);
          assert INDEX_SHIFT <= al_head->prev;
          extract_cell(cells, ncls, last_alloc);
        }
  @*/
  struct dchain_cell* alloc_head_prevp = cells + al_head->prev;
  alloc_head_prevp->next = allocated;
  al_head->prev = allocated;
  //@ assert(last_alloc != FREE_LIST_HEAD);
  //@ assert true == mem(allocated, fl);
  //@ alloc_prev_alloc_member(cls, al, ALLOC_LIST_HEAD, last_alloc);
  //@ assert true == mem(last_alloc, al);
  //@ if (last_alloc == allocated) { free_alloc_disjoint(cls, al, fl, allocated, nat_of_int(size));}
  //@ assert(last_alloc != allocated);
  //@ assume(last_alloc != allocated); //<-- TODO
  //@ assert(nth(last_alloc, cls) == nth(last_alloc, ncls));
  //@ dcell n_last_alloc = dcell(dchain_cell_get_prev(nth(last_alloc, cls)),allocated);
  //@ dcell n_al_head = dcell(allocated, dchain_cell_get_next(nth(ALLOC_LIST_HEAD,cls)));
  //@ list<dcell> rcls = update(ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls));
  //@ drop_update_unrelevant(INDEX_SHIFT, ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls));
  /*@ assert take(last_alloc-2, drop(2, update(ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls)))) == take(last_alloc-2, drop(2, update(last_alloc, n_last_alloc, ncls)));
    @*/
  //@ drop_update_relevant(INDEX_SHIFT, last_alloc, n_last_alloc, ncls);
  //@ take_update_unrelevant(last_alloc-INDEX_SHIFT, last_alloc-INDEX_SHIFT, n_last_alloc, drop(INDEX_SHIFT, ncls));
  //@ drop_update_unrelevant(last_alloc+1, ALLOC_LIST_HEAD, n_al_head, update(last_alloc, n_last_alloc, ncls));
  //@ drop_update_unrelevant(last_alloc+1, last_alloc, n_last_alloc, ncls);
  //@ glue_cells(cells, rcls, last_alloc);
  //@ attach_heads(cells, rcls);

  *index = allocated - INDEX_SHIFT;
  //@ length_tail(fl);
  //@ shift_inds_len(dchaini_alist_fp(dc), INDEX_SHIFT);
  //@ assert(length(dchaini_alist_fp(dc)) != size);

  //@ free_alloc_disjoint(cls, al, fl, allocated, nat_of_int(size));
  //@ assert(false == mem(allocated, al));
  //@ shift_inds_mem(dchaini_alist_fp(dc), INDEX_SHIFT, allocated);
  //@ assert(false == mem(allocated - INDEX_SHIFT, dchaini_alist_fp(dc)));

  //@ close dchainip(dchaini_allocate_fp(dc, allocated-INDEX_SHIFT), cells);
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

