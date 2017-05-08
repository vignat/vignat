#ifndef _VECTOR_H_INCLUDED_
#define _VECTOR_H_INCLUDED_

#define VECTOR_CAPACITY_UPPER_LIMIT 140000

struct Vector;

/*@
  predicate vectorp<t>(struct Vector* vector,
                       predicate (void*;t) entp,
                       list<t> values);
  predicate vector_accp<t>(struct Vector* vector,
                           predicate (void*;t) entp,
                           list<t> values,
                           int accessed_idx,
                           void* entry);
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
             length(contents) == capacity); @*/

void vector_borrow/*@ <t> @*/(struct Vector* vector, int index, void** val_out);
/*@ requires vectorp<t>(vector, ?entp, ?values) &*&
             0 <= index &*& index < length(values) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vector_accp<t>(vector, entp, values, index, vo) &*&
            entp(vo, nth(index, values)); @*/

void vector_return/*@ <t> @*/(struct Vector* vector, int index, void* value);
/*@ requires vector_accp<t>(vector, ?entp, ?values, index, value) &*&
             entp(value, ?v); @*/
/*@ ensures vectorp<t>(vector, entp, update(index, v, values)); @*/

#endif//_VECTOR_H_INCLUDED_
