#ifndef _ARRAY_BAT_H_INCLUDED_
#define _ARRAY_BAT_H_INCLUDED_

#include "../static-component-params.h"
#include "../containers/batcher.h"

#define ARRAY_BAT_EL_TYPE struct Batcher
#define ARRAY_BAT_CAPACITY RTE_MAX_ETHPORTS
#define ARRAY_BAT_EL_INIT batcher_init


#ifdef KLEE_VERIFICATION
struct ArrayBat
{
  char dummy;
};
#else//KLEE_VERIFICATION
struct ArrayBat
{
  struct Batcher data[ARRAY_BAT_CAPACITY];
};
#endif//KLEE_VERIFICATION

/*@ predicate some_batcherp(struct Batcher* p) = batcherp(_, p);
  @*/

/*@
  //params: list<struct rte_mbuf*> , batcherp
  predicate arrp_bat(list<list<struct rte_mbuf*> > data, struct ArrayBat *arr);
  predicate arrp_bat_acc(list<list<struct rte_mbuf*> > data, struct ArrayBat *arr,
                         int idx);

  fixpoint ARRAY_BAT_EL_TYPE *arrp_the_missing_cell_bat(struct ArrayBat *arr,
                                                        int idx) {
    return (ARRAY_BAT_EL_TYPE*)(arr->data)+idx;
  }

  lemma void construct_bat_element(ARRAY_BAT_EL_TYPE *p);
  requires p->len |-> ?l &*&
           pointers((void*)&p->batch, ARRAY_BAT_CAPACITY, _) &*&
           struct_Batcher_padding(p);
  ensures batcherp(_, p);

  @*/

void array_bat_init(struct ArrayBat *arr_out);
/*@ requires chars((void*)(arr_out),
                   ARRAY_BAT_CAPACITY*sizeof(ARRAY_BAT_EL_TYPE), _) &*&
             struct_ArrayBat_padding(arr_out); @*/
//@ ensures arrp_bat(_, arr_out);

ARRAY_BAT_EL_TYPE *array_bat_begin_access(struct ArrayBat *arr, int index);
//@ requires arrp_bat(?lst, arr) &*& 0 <= index &*& index < ARRAY_BAT_CAPACITY;
/*@ ensures arrp_bat_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_bat(arr, index) &*&
            batcherp(nth(index, lst), result) &*&
            length(nth(index, lst)) < BATCHER_CAPACITY; @*/

void array_bat_end_access(struct ArrayBat *arr);
/*@ requires arrp_bat_acc(?lst, arr, ?index) &*&
             batcherp(?x, arrp_the_missing_cell_bat(arr, index)) &*&
             length(x) < BATCHER_CAPACITY; @*/
//@ ensures arrp_bat(update(index, x, lst), arr);

#endif//_ARRAY_BAT_H_INCLUDED_
