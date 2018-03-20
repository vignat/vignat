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
                     list<pair<t, bool> > vals) =
    switch(vals) {
      case nil:
        return length == 0;
      case cons(h,t):
        return switch(h) {
          case pair(v, shared):
            return (shared ? entp(data, v) : [0.5]entp(data, v)) &*&
                   entsp(data + el_size,
                         el_size, entp,
                         length - 1,
                         t);
        };
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

  fixpoint list<void*> gen_vector_addrs_impl_fp<t>(void* data,
                                                   int el_size,
                                                   nat how_many) {
    switch(how_many) {
      case zero: return nil;
      case succ(n):
        return cons(data, gen_vector_addrs_impl_fp(data + el_size,
                                                   el_size,
                                                   n));
    }
  }

  fixpoint list<void*> gen_vector_addrs_fp<t>(void* data, int el_size, int cap) {
    return gen_vector_addrs_impl_fp(data, el_size, nat_of_int(cap));
  }

  predicate vectorp<t>(struct Vector* vector,
                       predicate (void*;t) entp,
                       list<pair<t, bool> > values,
                       list<void*> addrs) =
    vector_basep<t>(vector, ?el_size, ?cap, ?data) &*&
    cap == length(values) &*&
    entsp(data, el_size, entp, cap, values) &*&
    addrs == gen_vector_addrs_fp(data, el_size, cap);

  predicate vector_accp<t>(struct Vector* vector,
                           predicate (void*;t) entp,
                           list<pair<t, bool> > values,
                           list<void*> addrs,
                           int accessed_idx,
                           void* entry) =
    vector_basep<t>(vector, ?el_size, ?cap, ?data) &*&
    cap == length(values) &*&
    0 <= accessed_idx &*& accessed_idx < cap &*&
    entry == data + el_size*accessed_idx &*&
    addrs == gen_vector_addrs_fp(data, el_size, cap) &*&
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
                   len+1, append(lst, cons(pair(x, true), nil)));
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
        close entsp<t>(data, el_size, entp, 1, cons(pair(x, true), nil));
      case cons(h,t):
        append_to_entsp<t>(data + el_size, next_elem);
        close entsp<t>(data, el_size, entp,
                       len+1, append(lst, cons(pair(x, true), nil)));
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
               vectorp(new_vo, entp, ?contents, ?addrs) &*&
               length(contents) == capacity &*&
               true == forall(contents, snd)); @*/
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
  //@ list<pair<t, bool> > elems = nil;
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
                [_]is_vector_init_elem<t>(init_elem, entp, elem_size) &*&
                true == forall(elems, snd);
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
    //@ forall_append(elems, cons(pair(x, true), nil), snd);
    //@ elems = append(elems, cons(pair(x, true), nil));
  }
  //@ open upperbounded_ptr(_);
  //@ list<void*> addrs = gen_vector_addrs_fp((*vector_out)->data, elem_size, capacity);
  //@ close vectorp(*vector_out, entp, elems, addrs);
  return 1;
}

/*@
  lemma void extract_by_index_full<t>(char* data, int idx)
  requires entsp<t>(data, ?el_size, ?entp, ?cap, ?lst) &*&
           0 <= idx &*& idx < cap &*&
           nth(idx, lst) == pair(?val, true);
  ensures entsp<t>(data, el_size, entp, idx, take(idx, lst)) &*&
          entp(data + el_size*idx, val) &*&
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
          extract_by_index_full<t>(data + el_size, idx - 1);
          close entsp<t>(data, el_size, entp, idx, take(idx, lst));
        }
    }
  }
  @*/

/*@
  lemma void gen_addrs_index_impl(void* data, int el_size, int index, nat n)
  requires 0 <= index &*& index < int_of_nat(n);
  ensures nth(index, gen_vector_addrs_impl_fp(data, el_size, n)) == data + el_size*index;
  {
    switch(n) {
      case zero: return;
      case succ(m):
        if (index == 0) return;
        gen_addrs_index_impl(data + el_size, el_size, index - 1, m);
    }
  }

  lemma void gen_addrs_index(void* data, int el_size, int cap, int index)
  requires 0 <= index &*& index < cap;
  ensures nth(index, gen_vector_addrs_fp(data, el_size, cap)) == data + el_size*index;
  {
    gen_addrs_index_impl(data, el_size, index, nat_of_int(cap));
  }
  @*/

void vector_borrow_full/*@ <t> @*/(struct Vector* vector, int index, void** val_out)
/*@ requires vectorp<t>(vector, ?entp, ?values, ?addrs) &*&
             0 <= index &*& index < length(values) &*&
             nth(index, values) == pair(?val, true) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vector_accp<t>(vector, entp, values, addrs, index, vo) &*&
            vo == nth(index, addrs) &*&
            entp(vo, val); @*/
{
  //@ open vectorp<t>(vector, entp, values, addrs);
  //@ extract_by_index_full<t>(vector->data, index);
  //@ mul_mono_strict(index, length(values), vector->elem_size);
  //@ mul_bounds(index, length(values), vector->elem_size, 4096);
  *val_out = vector->data + index*vector->elem_size;
  //@ gen_addrs_index(vector->data, vector->elem_size, length(values), index);
  //@ close vector_accp<t>(vector, entp, values, addrs, index, *val_out);
}

/*@
  lemma void glue_by_index_full<t>(char* data, int idx, list<pair<t, bool> > lst)
  requires 0 <= idx &*& idx < length(lst) &*&
           entsp<t>(data, ?el_size, ?entp, idx, take(idx, lst)) &*&
           nth(idx, lst) == pair(?val, true) &*&
           entp(data + el_size*idx, val) &*&
           entsp<t>(data + el_size*(idx + 1), el_size, entp,
                    length(lst) - idx - 1, drop(idx + 1, lst));
  ensures entsp<t>(data, el_size, entp, length(lst), lst);
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        open entsp<t>(data, el_size, entp, idx, take(idx, lst));
        if (idx != 0) {
          glue_by_index_full(data + el_size, idx - 1, t);
        }
        close entsp<t>(data, el_size, entp, length(lst), lst);
    }
  }
  @*/

/*@
  lemma void extract_by_index_half<t>(char* data, int idx)
  requires entsp<t>(data, ?el_size, ?entp, ?cap, ?lst) &*&
           0 <= idx &*& idx < cap &*&
           nth(idx, lst) == pair(?val, false);
  ensures entsp<t>(data, el_size, entp, idx, take(idx, lst)) &*&
          [0.5]entp(data + el_size*idx, val) &*&
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
          extract_by_index_half<t>(data + el_size, idx - 1);
          close entsp<t>(data, el_size, entp, idx, take(idx, lst));
        }
    }
  }
  @*/
void vector_borrow_half/*@ <t> @*/(struct Vector* vector, int index, void** val_out)
/*@ requires vectorp<t>(vector, ?entp, ?values, ?addrs) &*&
             0 <= index &*& index < length(values) &*&
             nth(index, values) == pair(?val, false) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vector_accp<t>(vector, entp, values, addrs, index, vo) &*&
            vo == nth(index, addrs) &*&
            [0.5]entp(vo, val); @*/
{
  //@ open vectorp<t>(vector, entp, values, addrs);
  //@ extract_by_index_half<t>(vector->data, index);
  //@ mul_mono_strict(index, length(values), vector->elem_size);
  //@ mul_bounds(index, length(values), vector->elem_size, 4096);
  *val_out = vector->data + index*vector->elem_size;
  //@ gen_addrs_index(vector->data, vector->elem_size, length(values), index);
  //@ close vector_accp<t>(vector, entp, values, addrs, index, *val_out);
}

/*@
  lemma void glue_by_index_half<t>(char* data, int idx, list<pair<t, bool> > lst)
  requires 0 <= idx &*& idx < length(lst) &*&
           entsp<t>(data, ?el_size, ?entp, idx, take(idx, lst)) &*&
           nth(idx, lst) == pair(?val, false) &*&
           [0.5]entp(data + el_size*idx, val) &*&
           entsp<t>(data + el_size*(idx + 1), el_size, entp,
                    length(lst) - idx - 1, drop(idx + 1, lst));
  ensures entsp<t>(data, el_size, entp, length(lst), lst);
  {
    switch(lst) {
      case nil:
      case cons(h,t):
        open entsp<t>(data, el_size, entp, idx, take(idx, lst));
        if (idx != 0) {
          glue_by_index_half(data + el_size, idx - 1, t);
        }
        close entsp<t>(data, el_size, entp, length(lst), lst);
    }
  }
  @*/

void vector_return_full/*@ <t> @*/(struct Vector* vector, int index, void* value)
/*@ requires vector_accp<t>(vector, ?entp, ?values, ?addrs, index, value) &*&
             entp(value, ?v); @*/
/*@ ensures vectorp(vector, entp, update(index, pair(v, true), values), addrs); @*/
{
  //@ open vector_accp<t>(vector, entp, values, addrs, index, value);
  //@ take_update_unrelevant(index, index, pair(v, true), values);
  //@ drop_update_unrelevant(index + 1, index, pair(v, true), values);
  //@ glue_by_index_full(vector->data, index, update(index, pair(v, true), values));
  //@ close vectorp<t>(vector, entp, update(index, pair(v, true), values), addrs);
}


void vector_return_half/*@ <t> @*/(struct Vector* vector, int index, void* value)
/*@ requires vector_accp<t>(vector, ?entp, ?values, ?addrs, index, value) &*&
             [0.5]entp(value, ?v); @*/
/*@ ensures vectorp(vector, entp, update(index, pair(v, false), values), addrs); @*/
{
  //@ open vector_accp<t>(vector, entp, values, addrs, index, value);
  //@ take_update_unrelevant(index, index, pair(v, false), values);
  //@ drop_update_unrelevant(index + 1, index, pair(v, false), values);
  //@ glue_by_index_half(vector->data, index, update(index, pair(v, false), values));
  //@ close vectorp<t>(vector, entp, update(index, pair(v, false), values), addrs);
}


/*@
  lemma void vector_get_values_append<t>(list<pair<t, bool> > vector,
                                         list<int> indices,
                                         int index, t v)
  requires 0 <= index &*& index < length(vector) &*&
           nth(index, vector) == pair(v, _);
  ensures append(vector_get_values_fp(vector, indices), cons(v, nil)) ==
          vector_get_values_fp(vector, append(indices, cons(index, nil)));
  {
    switch(indices) {
      case nil: return;
      case cons(h,t):
        vector_get_values_append(vector, t, index, v);
    }
  }
  @*/

/*@
  lemma void vector_erase_keeps_val<t>(list<pair<t, bool> > vector,
                                       int erase_index, int val_index)
  requires 0 <= val_index &*& val_index < length(vector);
  ensures fst(nth(val_index, vector)) ==
          fst(nth(val_index, vector_erase_fp(vector, erase_index)));
  {
    switch(vector) {
      case nil: return;
      case cons(h,t):
        if (val_index == 0) {
          if (erase_index == 0) return;
          else return;
        }
        if (erase_index == 0) return;
        vector_erase_keeps_val(t, erase_index - 1, val_index - 1);
    }
  }

  lemma void vector_erase_all_same_length<t>(list<pair<t, bool> > vector,
                                             list<int> indices)
  requires true;
  ensures length(vector_erase_all_fp(vector, indices)) == length(vector);
  {
    switch(indices) {
      case nil: return;
      case cons(h,t):
        vector_erase_all_same_length(vector, t);
    }
  }

  lemma void vector_erase_all_keeps_val<t>(list<pair<t, bool> > vector,
                                           list<int> indices,
                                           int index)
  requires 0 <= index &*& index < length(vector);
  ensures fst(nth(index, vector_erase_all_fp(vector, indices))) ==
          fst(nth(index, vector));
  {
    switch(indices) {
      case nil: return;
      case cons(h,t):
        vector_erase_all_keeps_val(vector, t, index);
        vector_erase_all_same_length(vector, t);
        vector_erase_keeps_val(vector_erase_all_fp(vector, t), h, index);
    }
  }
  @*/

/*@
  lemma void vector_erase_swap<t>(list<pair<t, bool> > vector, int i1, int i2)
  requires true;
  ensures vector_erase_fp(vector_erase_fp(vector, i1), i2) ==
          vector_erase_fp(vector_erase_fp(vector, i2), i1);
  {
    switch(vector) {
      case nil: return;
      case cons(h,t):
        if (i1 == 0) return;
        if (i2 == 0) return;
        vector_erase_swap(t, i1 - 1, i2 - 1);
    }
  }

  lemma void vector_erase_one_more<t>(list<pair<t, bool> > vector,
                                      list<int> indices,
                                      int index)
  requires true;
  ensures vector_erase_fp(vector_erase_all_fp(vector, indices), index) ==
          vector_erase_all_fp(vector, append(indices, cons(index, nil)));
  {
    switch(indices) {
      case nil: return;
      case cons(h,t):
        vector_erase_one_more(vector, t, index);
        vector_erase_swap(vector_erase_all_fp(vector, t), index, h);
        assert vector_erase_fp(vector_erase_all_fp(vector, t), index) == vector_erase_all_fp(vector, append(t, cons(index, nil)));
        assert vector_erase_fp(vector_erase_fp(vector_erase_all_fp(vector, t), index), h) ==
               vector_erase_fp(vector_erase_all_fp(vector, append(t, cons(index, nil))), h);
        assert vector_erase_fp(vector_erase_fp(vector_erase_all_fp(vector, t), index), h) ==
               vector_erase_all_fp(vector, append(indices, cons(index, nil)));
    }
  }
  @*/
