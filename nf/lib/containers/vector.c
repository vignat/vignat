#include <stdlib.h>
#include <stdint.h>
#include "vector.h"

//@ #include "arith.gh"
//@ #include "stdex.gh"

struct Vector {
  char* data;
  int elem_size;
  int capacity;
};

/*@
  predicate entsp<t>(void* data, int el_size,
                     predicate (void*;t) entp,
                     int length,
                     list<t> vals) =
    switch(vals) {
      case nil:
        return length == 0;
      case cons(h,t):
        return entp(data, h) &*&
               entsp(data + el_size,
                     el_size, entp,
                     length - 1,
                     t);
    };

  predicate vector_basep<t>(struct Vector* vector;
                            int el_size,
                            int cap,
                            char* data) =
    malloc_block_Vector(vector) &*&
    vector->data |-> data &*&
    vector->elem_size |-> el_size &*&
    0 < el_size &*& el_size < 4096 &*&
    vector->capacity |-> cap &*&
    0 <= cap &*& cap < VECTOR_CAPACITY_UPPER_LIMIT &*&
    malloc_block(data, el_size*cap) &*&
    data + el_size*cap <= (void*)UINTPTR_MAX;


  predicate vectorp<t>(struct Vector* vector,
                       predicate (void*;t) entp,
                       list<t> values) =
    vector_basep<t>(vector, ?el_size, ?cap, ?data) &*&
    cap == length(values) &*&
    entsp(data, el_size, entp, cap, values);

  predicate vector_accp<t>(struct Vector* vector,
                           predicate (void*;t) entp,
                           list<t> values,
                           int accessed_idx,
                           void* entry) =
    vector_basep<t>(vector, ?el_size, ?cap, ?data) &*&
    cap == length(values) &*&
    0 <= accessed_idx &*& accessed_idx < cap &*&
    entry == data + el_size*accessed_idx &*&
    entsp(data, el_size, entp, accessed_idx, take(accessed_idx, values)) &*&
    entsp(data + el_size*(accessed_idx + 1), el_size, entp,
          cap - accessed_idx - 1, drop(accessed_idx + 1, values));
  @*/

/*@ predicate ptrs_eq(char* p1, int l, char* p2) = p1 == p2 + l;
  @*/

/*@
  lemma void append_to_entsp<t>(char* data, void* next_elem)
  requires entsp<t>(data, ?el_size, ?entp, ?len, ?lst) &*&
           entp(next_elem, ?x) &*&
           next_elem == (data + el_size*len) &*&
           len == length(lst);
  ensures entsp<t>(data, el_size, entp,
                   len+1, append(lst, cons(x, nil)));
  {
    close ptrs_eq(next_elem, el_size*len, data);
    open entsp(data, el_size, entp, len, lst);
    open ptrs_eq(next_elem, el_size*len, data);
    assert(next_elem == data + el_size*len);
    switch(lst) {
      case nil:
        assert len == 0;
        assert next_elem == data;
        close entsp<t>(data + el_size, el_size, entp, 0, nil);
        close entsp<t>(data, el_size, entp, 1, cons(x, nil));
      case cons(h,t):
        append_to_entsp<t>(data + el_size, next_elem);
        close entsp<t>(data, el_size, entp,
                       len+1, append(lst, cons(x, nil)));
    }
  }
  @*/


/*@
  predicate upperbounded_ptr(void* p) = true == ((p) <= (char *)UINTPTR_MAX);
  @*/

int vector_allocate/*@ <t> @*/(int elem_size, int capacity,
                               vector_init_elem* init_elem,
                               struct Vector** vector_out)
/*@ requires 0 < elem_size &*& 0 < capacity &*&
             [_]is_vector_init_elem<t>(init_elem, ?entp, elem_size) &*&
             0 <= elem_size &*& elem_size < 4096 &*&
             0 <= capacity &*& capacity < VECTOR_CAPACITY_UPPER_LIMIT &*&
             *vector_out |-> ?old_vo; @*/
/*@ ensures result == 0 ?
              (*vector_out |-> old_vo) :
              (*vector_out |-> ?new_vo &*&
               result == 1 &*&
               vectorp(new_vo, entp, ?contents) &*&
               length(contents) == capacity); @*/
{
  struct Vector* old_vector_val = *vector_out;
  struct Vector* vector_alloc = malloc(sizeof(struct Vector));
  if (vector_alloc == 0) return 0;
  *vector_out = (struct Vector*) vector_alloc;
  //@ mul_bounds(elem_size, 4096, capacity, VECTOR_CAPACITY_UPPER_LIMIT);
  char* data_alloc = malloc(elem_size*capacity);
  if (data_alloc == 0) {
    free(vector_alloc);
    *vector_out = old_vector_val;
    return 0;
  }
  (*vector_out)->data = data_alloc;
  (*vector_out)->elem_size = elem_size;
  (*vector_out)->capacity = capacity;
  //@ list<t> elems = nil;
  //@ close upperbounded_ptr((*vector_out)->data + elem_size*0);
  /*@ close entsp<t>((*vector_out)->data + elem_size*0, elem_size,
                     entp, 0, elems);
    @*/
  for (int i = 0; i < capacity; ++i)
    /*@
      invariant 0 <= i &*& i <= capacity &*&
                *vector_out |-> ?vec &*&
                vector_basep<t>(vec, elem_size, capacity, ?data) &*&
                true == ((char *)0 <= (data + elem_size*i)) &*&
                upperbounded_ptr(data + elem_size*i) &*&
                length(elems) == i &*&
                entsp(data, elem_size, entp, i, elems) &*&
                chars((data + elem_size*i),
                      elem_size*(capacity - i), _) &*&
                [_]is_vector_init_elem<t>(init_elem, entp, elem_size);
      @*/
    //@ decreases (capacity - i);
  {
    //@ open upperbounded_ptr(data + elem_size*i);
    //@ assert i < capacity;
    //@ chars_limits(data + elem_size*i);
    //@ assert 1 <= capacity - i;
    //@ mul_mono(1, capacity - i, elem_size);
    //@ chars_split(data + elem_size*i, elem_size);
    //@ assert 0 < elem_size;
    //@ mul_mono(0, i, elem_size);
    //@ assert 0 <= elem_size*i;
    init_elem((*vector_out)->data + elem_size*i);
    //@ assert entp(data + elem_size*i, ?x);
    //@ close upperbounded_ptr(data + elem_size*(i + 1));
    //@ append_to_entsp(data, data + elem_size*i);
    //@ elems = append(elems, cons(x, nil));
  }
  //@ open upperbounded_ptr(_);
  //@ close vectorp(*vector_out, entp, elems);
  return 1;
}

/*@
  lemma void extract_by_index<t>(char* data, int idx)
  requires entsp<t>(data, ?el_size, ?entp, ?cap, ?lst) &*&
           0 <= idx &*& idx < cap;
  ensures entsp<t>(data, el_size, entp, idx, take(idx, lst)) &*&
          entp(data + el_size*idx, nth(idx, lst)) &*&
          entsp<t>(data + el_size*(idx + 1), el_size, entp,
                   cap - idx - 1, drop(idx + 1, lst));
  {
    open entsp<t>(data, el_size, entp, cap, lst);
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
          close entsp<t>(data, el_size, entp, 0, nil);
        } else {
          extract_by_index<t>(data + el_size, idx - 1);
          close entsp<t>(data, el_size, entp, idx, take(idx, lst));
        }
    }
  }
  @*/

void vector_borrow/*@ <t> @*/(struct Vector* vector, int index, void** val_out)
/*@ requires vectorp<t>(vector, ?entp, ?values) &*&
             0 <= index &*& index < length(values) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vector_accp<t>(vector, entp, values, index, vo) &*&
            entp(vo, nth(index, values)); @*/
{
  //@ open vectorp<t>(vector, entp, values);
  //@ extract_by_index<t>(vector->data, index);
  //@ mul_mono_strict(index, length(values), vector->elem_size);
  //@ mul_bounds(index, length(values), vector->elem_size, 4096);
  *val_out = vector->data + index*vector->elem_size;
  //@ close vector_accp<t>(vector, entp, values, index, *val_out);
}

/*@
  lemma void glue_by_index<t>(char* data, int idx, list<t> lst)
  requires 0 <= idx &*& idx < length(lst) &*&
           entsp<t>(data, ?el_size, ?entp, idx, take(idx, lst)) &*&
           entp(data + el_size*idx, nth(idx, lst)) &*&
           entsp<t>(data + el_size*(idx + 1), el_size, entp,
                    length(lst) - idx - 1, drop(idx + 1, lst));
  ensures entsp<t>(data, el_size, entp, length(lst), lst);
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        open entsp<t>(data, el_size, entp, idx, take(idx, lst));
        if (idx != 0) {
          glue_by_index(data + el_size, idx - 1, t);
        }
        close entsp<t>(data, el_size, entp, length(lst), lst);
    }
  }
  @*/

void vector_return/*@ <t> @*/(struct Vector* vector, int index, void* value)
/*@ requires vector_accp<t>(vector, ?entp, ?values, index, value) &*&
             entp(value, ?v); @*/
/*@ ensures vectorp(vector, entp, update(index, v, values)); @*/
{
  //@ open vector_accp<t>(vector, entp, values, index, value);
  //@ take_update_unrelevant(index, index, v, values);
  //@ drop_update_unrelevant(index + 1, index, v, values);
  //@ glue_by_index(vector->data, index, update(index, v, values));
  //@ close vectorp<t>(vector, entp, update(index, v, values));
}
