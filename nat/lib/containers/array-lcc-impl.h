#include "array-lcc.h"

//@ #include "stdex.gh"
//@ #include "arith.gh"

/*@

  predicate lcore_conf_arrp(struct lcore_conf *lcp,
                            int len, list<lcore_confi> data) =
            switch(data) {
              case nil: return len == 0;
              case cons(h,t):
                return lcore_confp(h, lcp) &*&
                       lcore_conf_arrp(lcp+1,len-1,t) &*&
                       h == lcore_confi(2);
            };

  predicate arrp_lcc(list<lcore_confi> data, struct ArrayLcc *arr) =
    true == ((char *)0 <=
             (void*)((ARRAY_LCC_EL_TYPE*)(arr->data))) &*&
    true == ((void*)((ARRAY_LCC_EL_TYPE*)(arr->data) +
                     ARRAY_LCC_CAPACITY) <=
             (char *)UINTPTR_MAX) &*&
    length(data) == ARRAY_LCC_CAPACITY &*&
    lcore_conf_arrp(arr->data, ARRAY_LCC_CAPACITY, data);

  predicate arrp_lcc_acc(list<lcore_confi> data, struct ArrayLcc *arr, int idx) =
    0 <= idx &*& idx < ARRAY_LCC_CAPACITY &*&
    true == ((char *)0 <=
             (void*)((ARRAY_LCC_EL_TYPE*)(arr->data))) &*&
    true == ((void*)((ARRAY_LCC_EL_TYPE*)(arr->data) +
                     ARRAY_LCC_CAPACITY) <=
             (char *)UINTPTR_MAX) &*&
    length(data) == ARRAY_LCC_CAPACITY &*&
    lcore_conf_arrp(arr->data, idx, take(idx, data)) &*&
    lcore_conf_arrp((ARRAY_LCC_EL_TYPE*)(arr->data)+idx+1,
                    ARRAY_LCC_CAPACITY - idx - 1, drop(idx+1,data));
  @*/

static void lcore_conf_condition(struct lcore_conf *cell)
//@ requires chars((void*)cell, sizeof(struct lcore_conf), _);
//@ ensures lcore_confp(lcore_confi(2), cell);
{
  //@ close_struct(cell);
#ifdef KLEE_VERIFICATION
  // VVV Here was a bug: "<" instead of "<=" which caused this model to
  // loose some outputs !
  klee_assume(0 <= cell->n_rx_queue);
  klee_assume(cell->n_rx_queue < MAX_RX_QUEUE_PER_LCORE);
#else//KLEE_VERIFICATION
  cell->n_rx_queue = 2;
#endif//KLEE_VERIFICATION
  array_rq_init(&cell->rx_queue_list);
  array_u16_init(&cell->tx_queue_id);
  array_bat_init(&cell->tx_mbufs);
  //@ construct_lcc_element(cell);
}

#ifdef KLEE_VERIFICATION

#include <klee/klee.h>

ARRAY_LCC_EL_TYPE array_lcc_model_cell;
int array_lcc_allocated_index;
int array_lcc_index_allocated;
struct ArrayLcc *array_lcc_initialized;
int array_lcc_cell_is_exposed;

void array_lcc_init(struct ArrayLcc *arr_out)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr_out, sizeof(struct ArrayLcc), "arr_out");
  klee_make_symbolic(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "array_lcc_model_cell");
  array_lcc_index_allocated = 0;
  ARRAY_LCC_EL_INIT(&array_lcc_model_cell);
  array_lcc_initialized = arr_out;
  klee_forbid_access(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "array lcc private state");
  array_lcc_cell_is_exposed = 0;
}

void array_lcc_reset(struct ArrayLcc *arr)
{
  //Non traceable function.
  klee_assert(arr == array_lcc_initialized);
  if (!array_lcc_cell_is_exposed)
    klee_allow_access(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE));
  klee_make_symbolic(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "array_lcc_model_cell");
  ARRAY_LCC_EL_INIT(&array_lcc_model_cell);
  if (!array_lcc_cell_is_exposed)
    klee_forbid_access(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                       "private state");
}

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index)
{
  klee_trace_ret_ptr(sizeof(ARRAY_LCC_EL_TYPE));
  ARRAY_LCC_EL_TRACE_BREAKDOWN;
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayLcc), "arr");
  klee_trace_param_i32(index, "index");

  klee_assert(arr == array_lcc_initialized);
  if (array_lcc_index_allocated) {
    klee_assert(index == array_lcc_allocated_index);
  } else {
    array_lcc_allocated_index = index;
    array_lcc_index_allocated = 1;
  }
  klee_allow_access(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE));
  array_lcc_cell_is_exposed = 1;
  return &array_lcc_model_cell;
}

void array_lcc_end_access(struct ArrayLcc *arr)
{
  klee_trace_ret();
  klee_trace_param_just_ptr(arr, sizeof(struct ArrayLcc), "arr");
  klee_assert(array_lcc_index_allocated);
  klee_assert(arr == array_lcc_initialized);
  klee_trace_extra_ptr(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                       "returned_cell");
  ARRAY_LCC_EL_TRACE_EP_BREAKDOWN(&array_lcc_model_cell);

  klee_forbid_access(&array_lcc_model_cell, sizeof(ARRAY_LCC_EL_TYPE),
                     "private state");
  array_lcc_cell_is_exposed = 1;
  //nothing
}

#else//KLEE_VERIFICATION


/*@ predicate ptrs_eq(ARRAY_LCC_EL_TYPE* p1, int l, ARRAY_LCC_EL_TYPE* p2) =
      p1 == p2 + l;
  @*/

/*@
  lemma void append_to_arr(ARRAY_LCC_EL_TYPE* arr, ARRAY_LCC_EL_TYPE* el)
  requires lcore_conf_arrp(arr, ?len, ?lst) &*& lcore_confp(?v, el) &*&
           el == (arr + len) &*& len == length(lst) &*&
           v == lcore_confi(2);
  ensures lcore_conf_arrp(arr, len+1, append(lst, cons(v, nil)));
  {
    close ptrs_eq(el, len, arr);
    open lcore_conf_arrp(arr, len, lst);
    open ptrs_eq(el, len, arr);
    assert(el == arr + len);
    switch(lst) {
      case nil:
        close lcore_conf_arrp(arr+1, 0, nil);
        close lcore_conf_arrp(arr, 1, cons(v, nil));
      case cons(h,t):
        append_to_arr(arr+1, el);
        close lcore_conf_arrp(arr, len+1, append(lst, cons(v, nil)));
    }
  }
  @*/

/*@
  predicate upperbounded_ptr(void* p) = true == ((p) <= (char *)UINTPTR_MAX);
  @*/

void array_lcc_init(struct ArrayLcc *arr_out)
/*@ requires chars(arr_out->data,
             sizeof(ARRAY_LCC_EL_TYPE)*ARRAY_LCC_CAPACITY, _);@*/
/*@ ensures arrp_lcc(?lst, arr_out) &*&
            length(lst) == ARRAY_LCC_CAPACITY; @*/
{
  int i;
  //@ close lcore_conf_arrp(arr_out->data, 0, nil);
  //@ close upperbounded_ptr((ARRAY_LCC_EL_TYPE*)(arr_out->data) + 0);
  for (i = 0; i < ARRAY_LCC_CAPACITY; ++i)
    /*@
      invariant 0 <= i &*& i <= ARRAY_LCC_CAPACITY &*&
                true == ((char *)0 <=
                         (void*)((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i)) &*&
                upperbounded_ptr((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i) &*&
                lcore_conf_arrp(arr_out->data, i, ?lst) &*&
                length(lst) == i &*&
                chars((void*)((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i),
                      sizeof(ARRAY_LCC_EL_TYPE)*
                      (ARRAY_LCC_CAPACITY-i), _);
      @*/
    //@ decreases ARRAY_LCC_CAPACITY - i;
  {
    //@ open upperbounded_ptr((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i);
    //@ assert i < ARRAY_LCC_CAPACITY;
    //@ chars_limits((void*)((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i));
    //@ assert lcore_conf_arrp(arr_out->data, i, ?xxx);

    //@ assert 1 <= ARRAY_LCC_CAPACITY-i;
    //@ mul_mono(1, ARRAY_LCC_CAPACITY-i, sizeof(ARRAY_LCC_EL_TYPE));
    /*@ chars_split((void*)((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i),
                    sizeof(ARRAY_LCC_EL_TYPE));
                    @*/
    ARRAY_LCC_EL_INIT((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i);
    //@ assert lcore_confp(?xx, (ARRAY_LCC_EL_TYPE*)(arr_out->data) + i);
    /*@ append_to_arr((ARRAY_LCC_EL_TYPE*)(arr_out->data),
                      (ARRAY_LCC_EL_TYPE*)(arr_out->data) + i);
                      @*/
    //@ close upperbounded_ptr((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i + 1);
  }
  //@ open upperbounded_ptr((ARRAY_LCC_EL_TYPE*)(arr_out->data) + i);
  //@ assert i == ARRAY_LCC_CAPACITY;
  //@ assert lcore_conf_arrp(arr_out->data, ARRAY_LCC_CAPACITY, ?lst);
  //@ close arrp_lcc(lst, arr_out);
}

/*@
  lemma void extract_by_index(ARRAY_LCC_EL_TYPE* arr, int idx)
  requires lcore_conf_arrp(arr, ?len, ?lst) &*& 0 <= idx &*& idx < len;
  ensures lcore_conf_arrp(arr, idx, take(idx, lst)) &*&
          lcore_confp(nth(idx, lst), arr + idx) &*&
          lcore_conf_arrp(arr+idx+1, len - idx - 1, drop(idx+1,lst)) &*&
          nth(idx, lst) == lcore_confi(2);
  {
    open lcore_conf_arrp(arr, len, lst);
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
          close lcore_conf_arrp(arr, 0, nil);
        } else {
          extract_by_index(arr+1, idx-1);
          close lcore_conf_arrp(arr, idx, take(idx, lst));
        }
    }
  }
  @*/


ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index)
//@ requires arrp_lcc(?lst, arr) &*& 0 <= index &*& index < ARRAY_LCC_CAPACITY;
/*@ ensures arrp_lcc_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_lcc(arr, index) &*&
            lcore_confp(nth(index, lst), result) &*&
            nth(index, lst) == lcore_confi(2);
  @*/
{
  //@ open arrp_lcc(lst, arr);
  //@ extract_by_index(arr->data, index);
  //@ assert true == (index < ARRAY_LCC_CAPACITY);
  //@ mul_mono_strict(index, ARRAY_LCC_CAPACITY, sizeof(ARRAY_LCC_EL_TYPE));
  return (ARRAY_LCC_EL_TYPE*)(arr->data) + index;
  //@ close arrp_lcc_acc(lst, arr, index);
}

/*@
  lemma void glue_array(ARRAY_LCC_EL_TYPE* arr, int idx,
                        list<lcore_confi> lst)
  requires lcore_conf_arrp(arr, idx, take(idx, lst)) &*&
           lcore_confp(nth(idx, lst), arr + idx) &*&
           lcore_conf_arrp(arr+idx+1, length(lst) - idx - 1,
                           drop(idx+1,lst)) &*&
           0 <= idx &*& idx < length(lst) &*&
           nth(idx, lst) == lcore_confi(2);
  ensures lcore_conf_arrp(arr, length(lst), lst);
  {
    open lcore_conf_arrp(arr, idx, take(idx, lst));
    switch(lst) {
      case nil:
      case cons(h,t):
        if (idx == 0) {
        } else {
          glue_array(arr+1, idx-1, t);
        }
    }
    close lcore_conf_arrp(arr, length(lst), lst);
  }
  @*/

void array_lcc_end_access(struct ArrayLcc *arr)
/*@ requires arrp_lcc_acc(?lst, arr, ?idx) &*&
             lcore_confp(?lc, arrp_the_missing_cell_lcc(arr, idx)) &*&
             lc == lcore_confi(2); @*/
/*@ ensures arrp_lcc(update(idx, lc, lst), arr) &*&
            length(update(idx, lc, lst)) == ARRAY_LCC_CAPACITY; @*/
{
  //@ open arrp_lcc_acc(lst, arr, idx);
  //@ take_update_unrelevant(idx, idx, lc, lst);
  //@ nth_update(idx, idx, lc, lst);
  //@ drop_update_unrelevant(idx+1, idx, lc, lst);
  //@ glue_array(arr->data, idx, update(idx, lc, lst));
  IGNORE(arr);
  //@ close arrp_lcc(update(idx, lc, lst), arr);
}

/*@
  lemma void construct_lcc_element(ARRAY_LCC_EL_TYPE *p)
  requires p->n_rx_queue |-> ?nrq &*&
           0 <= nrq &*& nrq < MAX_RX_QUEUE_PER_LCORE &*&
           arrp_rq(_, &p->rx_queue_list) &*&
           arrp_u16(_, &p->tx_queue_id) &*&
           arrp_bat(_, &p->tx_mbufs) &*&
           struct_lcore_conf_padding(p);
  ensures lcore_confp(lcore_confi(nrq), p);
  {
    close lcore_confp(lcore_confi(nrq), p);
  }
  @*/


#endif//KLEE_VERIFICATION
