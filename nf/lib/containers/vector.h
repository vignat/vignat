#ifndef _VECTOR_H_INCLUDED_
#define _VECTOR_H_INCLUDED_

//@ #include "stdex.gh"
//@ #include "listexex.gh"

#define VECTOR_CAPACITY_UPPER_LIMIT 140000

struct Vector;

/*@
  predicate vectorp<t>(struct Vector* vector,
                       predicate (void*;t) entp,
                       list<pair<t, bool> > values);

  fixpoint list<pair<t, bool> > vector_erase_fp<t>(list<pair<t, bool> > vector,
                                                   int index) {
    return update(index, pair(fst(nth(index, vector)), true), vector);
  }

  predicate vector_accp<t>(struct Vector* vector,
                           predicate (void*;t) entp,
                           list<pair<t, bool> > values,
                           int accessed_idx,
                           void* entry);

  fixpoint list<pair<t, bool> > vector_erase_all_fp<t>(list<pair<t, bool> > vector,
                                                       list<int> indices) {
    switch(indices) {
      case nil: return vector;
      case cons(h,t):
        return vector_erase_fp(vector_erase_all_fp(vector, t), h);
    }
  }

  fixpoint list<t> vector_get_values_fp<t>(list<pair<t, bool> > vector,
                                           list<int> indices) {
    return map((sup)(fst, (nth2)(vector)), indices);
  }
  @*/

/*@
  lemma void vector_erase_all_same_len<t>(list<pair<t, bool> > vector,
                                          list<int> indices);
  requires true;
  ensures length(vector) == length(vector_erase_all_fp(vector, indices));
  @*/

/*@
  lemma void vector_get_values_append<t>(list<pair<t, bool> > vector,
                                         list<int> indices,
                                         int index, t v);
  requires 0 <= index &*& index < length(vector) &*&
           nth(index, vector) == pair(v, _);
  ensures append(vector_get_values_fp(vector, indices), cons(v, nil)) ==
          vector_get_values_fp(vector, append(indices, cons(index, nil)));
  @*/

/*@
  lemma void vector_erase_all_keeps_val<t>(list<pair<t, bool> > vector,
                                           list<int> indices,
                                           int index);
  requires 0 <= index &*& index < length(vector);
  ensures fst(nth(index, vector_erase_all_fp(vector, indices))) ==
          fst(nth(index, vector));
  @*/

/*@
   lemma void vector_erase_one_more<t>(list<pair<t, bool> > vector,
                                       list<int> indices,
                                       int index);
   requires true;
   ensures vector_erase_fp(vector_erase_all_fp(vector, indices), index) ==
           vector_erase_all_fp(vector, append(indices, cons(index, nil)));
  @*/

typedef void vector_init_elem/*@ <t> (predicate (void*;t) entp,
                                      int elem_size) @*/
                             (void* elem);
/*@ requires chars(elem, elem_size, _); @*/
/*@ ensures entp(elem, _); @*/

int vector_allocate/*@ <t> @*/(int elem_size, int capacity,
                               vector_init_elem* init_elem,
                               struct Vector** vector_out);
/*@ requires 0 < elem_size &*& 0 < capacity &*&
             [_]is_vector_init_elem<t>(init_elem, ?entp, elem_size) &*&
             0 <= elem_size &*& elem_size < 4096 &*&
             0 <= capacity &*& capacity < VECTOR_CAPACITY_UPPER_LIMIT &*&
             *vector_out |-> ?old_vo; @*/
/*@ ensures result == 0 ?
            (*vector_out |-> old_vo) :
            (*vector_out |-> ?new_vo &*&
             result == 1 &*&
             vectorp<t>(new_vo, entp, ?contents) &*&
             length(contents) == capacity &*&
             true == forall(contents, snd)); @*/

void vector_borrow_full/*@ <t> @*/(struct Vector* vector, int index, void** val_out);
/*@ requires vectorp<t>(vector, ?entp, ?values) &*&
             0 <= index &*& index < length(values) &*&
             nth(index, values) == pair(?val, true) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vector_accp<t>(vector, entp, values, index, vo) &*&
            entp(vo, val); @*/

void vector_borrow_half/*@ <t> @*/(struct Vector* vector, int index, void** val_out);
/*@ requires vectorp<t>(vector, ?entp, ?values) &*&
             0 <= index &*& index < length(values) &*&
             nth(index, values) == pair(?val, false) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vector_accp<t>(vector, entp, values, index, vo) &*&
            [0.5]entp(vo, val); @*/

void vector_return_full/*@ <t> @*/(struct Vector* vector, int index, void* value);
/*@ requires vector_accp<t>(vector, ?entp, ?values, index, value) &*&
             entp(value, ?v); @*/
/*@ ensures vectorp<t>(vector, entp, update(index, pair(v, true), values)); @*/

void vector_return_half/*@ <t> @*/(struct Vector* vector, int index, void* value);
/*@ requires vector_accp<t>(vector, ?entp, ?values, index, value) &*&
             [0.5]entp(value, ?v); @*/
/*@ ensures vectorp<t>(vector, entp, update(index, pair(v, false), values)); @*/

#endif//_VECTOR_H_INCLUDED_
