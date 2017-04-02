#ifndef _DOUBLE_CHAIN_IMPL_H_INCLUDED_
#define _DOUBLE_CHAIN_IMPL_H_INCLUDED_

struct dchain_cell {
    int prev;
    int next;
};
/**
 * Requires the array dchain_cell, large enough to fit all the range of
 * possible 'index' values + 2 special values.
 * Forms a two closed linked lists inside the array.
 * First list represents the "free" cells. It is a single linked list.
 * Initially the whole array
 * (except 2 special cells holding metadata) added to the "free" list.
 * Second list represents the "occupied" cells and it is double-linked,
 * the order matters.
 * It is supposed to store the ordered sequence, and support moving any
 * element to the top.
 *
 * The lists are organized as follows:
 *              +----+   +---+   +-------------------+   +-----
 *              |    V   |   V   |                   V   |
 *  [. + .][    .]  {    .} {    .} {. + .} {. + .} {    .} ....
 *   ^   ^                           ^   ^   ^   ^
 *   |   |                           |   |   |   |
 *   |   +---------------------------+   +---+   +-------------
 *   +---------------------------------------------------------
 *
 * Where {    .} is an "free" list cell, and {. + .} is an "alloc" list cell,
 * and dots represent prev/next fields.
 * [] - denote the special cells - the ones that are always kept in the
 * corresponding lists.
 * Empty "alloc" and "free" lists look like this:
 *
 *   +---+   +---+
 *   V   V   V   |
 *  [. + .] [    .]
 *
 * , i.e. cells[0].next == 0 && cells[0].prev == 0 for the "alloc" list, and
 * cells[1].next == 1 for the free list.
 * For any cell in the "alloc" list, 'prev' and 'next' fields must be different.
 * Any cell in the "free" list, in contrast, have 'prev' and 'next' equal;
 * After initialization, any cell is allways on one and only one of these lists.
 */

#define DCHAIN_RESERVED (2)

/*@
  inductive dcell = dcell(int, int);
  fixpoint int dchain_cell_get_prev(dcell dc) {
     switch(dc) {case dcell(prev, next): return prev;}
  }
  fixpoint int dchain_cell_get_next(dcell dc) {
     switch(dc) {case dcell(prev, next): return next;}
  }
  predicate dcellp(struct dchain_cell* cell; dcell dc) =
            cell->prev |-> ?prev &*&
            cell->next |-> ?next &*&
            dc == dcell(prev, next);

  predicate dcellsp(struct dchain_cell* cell, int count; list<dcell> dcs) =
      count == 0 ?
        dcs == nil
      :
        dcellp(cell, ?dc) &*& dcellsp(cell + 1, count - 1, ?dcs0) &*&
        dcs == cons(dc, dcs0);

  // reserved indexes with resprective times, index_range
  inductive dchaini = dchaini(list<int>, int);

  predicate dchainip(dchaini ch,
                     struct dchain_cell * cells);

  fixpoint dchaini empty_dchaini_fp(int index_range) {
    return dchaini(nil, index_range);
  }

  fixpoint bool dchaini_out_of_space_fp(dchaini ch) {
    switch(ch) { case dchaini(alist, size):
      return size <= length(alist);
    }
  }

  fixpoint bool dchaini_allocated_fp(dchaini ch, int idx) {
    switch(ch) { case dchaini(alist, size):
      return mem(idx, alist);
    }
  }

  fixpoint dchaini dchaini_allocate_fp(dchaini ch, int idx) {
    switch(ch) { case dchaini(alist, size):
      return dchaini(append(alist, cons(idx, nil)), size);
    }
  }

  fixpoint dchaini dchaini_rejuvenate_fp(dchaini ch, int index) {
    switch(ch) { case dchaini(alist, size):
      return dchaini(append(remove(index, alist), cons(index, nil)), size);
    }
  }

  fixpoint bool dchaini_is_empty_fp(dchaini ch) {
    switch(ch) { case dchaini(alist, size): return alist == nil; }
  }

  fixpoint int dchaini_get_oldest_index_fp(dchaini ch) {
    switch(ch) { case dchaini(alist, size):
      return head(alist);
    }
  }

  fixpoint dchaini dchaini_remove_fp(dchaini ch, int index) {
    switch(ch) { case dchaini(alist, size):
      return dchaini(remove(index, alist), size);
    }
  }

  fixpoint int dchaini_irange_fp(dchaini ch) {
    switch(ch) { case dchaini(alist, size): return size; }
  }

  fixpoint list<int> dchaini_alist_fp(dchaini dc) {
    switch(dc) { case dchaini(alist, size): return alist; }
  }

  @*/

/*@
  lemma void dcell_layout_assumptions(struct dchain_cell* p);
  requires true;
  ensures sizeof(struct dchain_cell) == sizeof(int) + sizeof(int) &*&
          true == ((void*)&p->prev + sizeof(int) == (void*)&p->next);
  @*/

/*@
  lemma void dchaini_no_dups(struct dchain_cell *cells, dchaini dc, int index);
  requires dchainip(dc, cells);
  ensures dchainip(dc, cells) &*&
          false == dchaini_allocated_fp(dchaini_remove_fp(dc, index), index);

  lemma void dchaini_alist_upperbound(struct dchain_cell *cells, dchaini dc);
  requires dchainip(dc, cells);
  ensures dchainip(dc, cells) &*&
          length(dchaini_alist_fp(dc)) <= dchaini_irange_fp(dc);
  @*/


void dchain_impl_init(struct dchain_cell *cells, int index_range);
/*@ requires 0 < index_range &*&
             index_range < INT_MAX - 2 &*&
             dcellsp(cells, index_range + DCHAIN_RESERVED, _); @*/
/*@ ensures dchainip(empty_dchaini_fp(index_range), cells); @*/

int dchain_impl_allocate_new_index(struct dchain_cell *cells, int *index);
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

int dchain_impl_free_index(struct dchain_cell *cells, int index);
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_fp(dc, index) ?
             (dchainip(dchaini_remove_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/

int dchain_impl_get_oldest_index(struct dchain_cell *cells, int *index);
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

int dchain_impl_rejuvenate_index(struct dchain_cell *cells, int index);
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_fp(dc, index) ?
             (dchainip(dchaini_rejuvenate_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/

#endif //_DOUBLE_CHAIN_IMPL_H_INCLUDED_
