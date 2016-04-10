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
 *       +-----------+   +---+   +-------------------+   +-----
 *       |           V   |   V   |                   V   |    
 *  [    .] [. + .] {    .} {    .} {. + .} {. + .} {    .} ....
 *           ^   ^   ^   ^           ^   ^   ^   ^
 *           |   |   |   |           |   |   |   |
 *           |   +---+   +-----------+   +---+   +-------------
 *           +-------------------------------------------------
 *
 * Where {    .} is an "free" list cell, and {. + .} is an "occupied" list cell,
 * and dots represent prev/next fields.
 * [] - denote the special cells - the ones that are always kept in the
 * corresponding lists.
 * Empty "free" and "allocated" lists look like this:
 *
 *  +---+    +---+
 *  |   V    V   V
 * [    .]  [. + .]
 *
 * , or cells[0].next == 0 && cells[0].prev == 0 for the "alloc" list, and
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

  fixpoint dchaini empty_dchaini_fp(int index_range);
  fixpoint bool dchaini_out_of_space_fp(dchaini ch);
  fixpoint int dchaini_get_next_index_fp(dchaini ch);
  fixpoint dchaini dchaini_take_next_index_fp(dchaini ch);
  fixpoint dchaini dchaini_rejuvenate_fp(dchaini ch, int index);
  fixpoint bool dchaini_allocated_index_fp(dchaini ch, int index);
  fixpoint bool dchaini_is_empty_fp(dchaini ch);
  fixpoint int dchaini_get_oldest_index_fp(dchaini ch);
  fixpoint dchaini dchaini_remove_index_fp(dchaini ch, int index);
  fixpoint int dchaini_irange_fp(dchaini ch);
  @*/

void dchain_impl_init(struct dchain_cell *cells, int index_range);
/*@ requires 0 < index_range &*&
             dcellsp(cells, index_range + DCHAIN_RESERVED, _); @*/
/*@ ensures dchainip(empty_dchaini_fp(index_range), cells); @*/

int dchain_impl_allocate_new_index(struct dchain_cell *cells, int *index);
/*@ requires dchainip(?dc, cells) &*& *index |-> ?i; @*/
/*@ ensures (dchaini_out_of_space_fp(dc) ?
             (dchainip(dc, cells) &*& *index |-> i &*& result == 0) :
             (dchainip(dchaini_take_next_index_fp(dc), cells) &*&
              *index |-> dchaini_get_next_index_fp(dc) &*&
              result == 1)); @*/

int dchain_impl_free_index(struct dchain_cell *cells, int index);
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_index_fp(dc, index) ?
             (dchainip(dchaini_remove_index_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/

int dchain_impl_get_oldest_index(struct dchain_cell *cells, int *index);
/*@ requires dchainip(?dc, cells) &*& *index |-> ?i; @*/
/*@ ensures dchainip(dc, cells) &*&
            (dchaini_is_empty_fp(dc) ?
             (*index |-> i &*&
              result == 0) :
             (*index |-> dchaini_get_oldest_index_fp(dc) &*&
              result == 1)); @*/
int dchain_impl_rejuvenate_index(struct dchain_cell *cells, int index);
/*@ requires dchainip(?dc, cells) &*&
             0 <= index &*& index < dchaini_irange_fp(dc); @*/
/*@ ensures (dchaini_allocated_index_fp(dc, index) ?
             (dchainip(dchaini_rejuvenate_fp(dc, index), cells) &*&
              result == 1) :
             (dchainip(dc, cells) &*&
              result == 0)); @*/

#endif //_DOUBLE_CHAIN_IMPL_H_INCLUDED_
