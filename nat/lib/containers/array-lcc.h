#ifndef _ARRAY_LCC_H_INCLUDED_
#define _ARRAY_LCC_H_INCLUDED_

#include <stdint.h>
#include "../ignore.h"
#include "../static-component-params.h"
#include "../containers/array-rq.h"
#include "../containers/array-u16.h"
#include "../containers/array-bat.h"

struct lcore_conf {
  uint16_t n_rx_queue;
  struct ArrayRq rx_queue_list;
  struct ArrayU16 tx_queue_id;
  struct ArrayBat tx_mbufs;
}
#ifdef _NO_VERIFAST_
  __rte_cache_aligned;
#else//_NO_VERIFAST_
;
#endif//_NO_VERIFAST_

#define ARRAY_LCC_EL_TYPE struct lcore_conf
#define ARRAY_LCC_CAPACITY RTE_MAX_LCORE
#define ARRAY_LCC_SUFFIX _lconf
#define ARRAY_LCC_EL_INIT lcore_conf_condition
//TODO: add support in Klee for detailed dumping of the
// return pointee (including pointees for pointer fields)
#define ARRAY_LCC_EL_TRACE_BREAKDOWN {                                  \
    klee_trace_ret_ptr_field(offsetof(struct lcore_conf, n_rx_queue),   \
                             sizeof(uint16_t), "n_rx_queue");           \
    klee_trace_ret_ptr_field_just_ptr                                   \
      (offsetof(struct lcore_conf, rx_queue_list),                      \
       sizeof(struct ArrayRq), "rx_queue_list");                        \
    klee_trace_ret_ptr_field_just_ptr                                   \
      (offsetof(struct lcore_conf, tx_queue_id),                        \
       sizeof(struct ArrayU16), "tx_queue_id");                         \
    klee_trace_ret_ptr_field_just_ptr                                   \
      (offsetof(struct lcore_conf, tx_mbufs),                           \
       sizeof(struct ArrayBat), "tx_mbufs");                            \
  }
#define ARRAY_LCC_EL_TRACE_ARG_BREAKDOWN(arg) {                         \
    klee_trace_param_ptr_field(arg, offsetof(struct lcore_conf, n_rx_queue), \
                               sizeof(uint16_t), "n_rx_queue");         \
    klee_trace_param_ptr_field_just_ptr                                 \
      (arg, offsetof(struct lcore_conf, rx_queue_list),                 \
       sizeof(struct ArrayRq), "rx_queue_list");                        \
    klee_trace_param_ptr_field_just_ptr                                 \
      (arg, offsetof(struct lcore_conf, tx_queue_id),                   \
       sizeof(struct ArrayU16), "tx_queue_id");                         \
    klee_trace_param_ptr_field_just_ptr                                 \
      (arg, offsetof(struct lcore_conf, tx_mbufs),                      \
       sizeof(struct ArrayBat), "tx_mbufs");                            \
  }
#define ARRAY_LCC_EL_TRACE_EP_BREAKDOWN(ep) {                           \
    klee_trace_extra_ptr_field(ep, offsetof(struct lcore_conf, n_rx_queue), \
                               sizeof(uint16_t), "n_rx_queue");         \
    klee_trace_extra_ptr_field_just_ptr                                 \
      (ep, offsetof(struct lcore_conf, rx_queue_list),                  \
       sizeof(struct ArrayRq), "rx_queue_list");                        \
    klee_trace_extra_ptr_field_just_ptr                                 \
      (ep, offsetof(struct lcore_conf, tx_queue_id),                    \
       sizeof(struct ArrayU16), "tx_queue_id");                         \
    klee_trace_extra_ptr_field_just_ptr                                 \
      (ep, offsetof(struct lcore_conf, tx_mbufs),                       \
       sizeof(struct ArrayBat), "tx_mbufs");                            \
  }

#ifdef KLEE_VERIFICATION
struct ArrayLcc {
  char dummy;
};
#else//KLEE_VERIFICATION
struct ArrayLcc
{
  ARRAY_LCC_EL_TYPE data[ARRAY_LCC_CAPACITY];
};
#endif//KLEE_VERIFICATION

/*@
  inductive lcore_confi = lcore_confi(int);
  predicate lcore_confp(lcore_confi lc, struct lcore_conf *lcp) =
      struct_lcore_conf_padding(lcp) &*&
      lcp->n_rx_queue |-> ?nrq &*&
      lc == lcore_confi(nrq) &*&
      0 <= nrq &*& nrq < MAX_RX_QUEUE_PER_LCORE &*&
      arrp_rq(_, &lcp->rx_queue_list) &*&
      arrp_u16(_, &lcp->tx_queue_id) &*&
      arrp_bat(_, &lcp->tx_mbufs);
  predicate some_lcore_confp(struct lcore_conf *lcp) = lcore_confp(?lc, lcp) &*&
            lc == lcore_confi(2);
  @*/

/*@
//params: lcore_confi, lcore_confp
predicate arrp_lcc(list<lcore_confi> data, struct ArrayLcc *arr);
predicate arrp_lcc_acc(list<lcore_confi> data, struct ArrayLcc *arr, int idx);
fixpoint ARRAY_LCC_EL_TYPE *arrp_the_missing_cell_lcc(struct ArrayLcc *arr,
                                                      int idx) {
  return (ARRAY_LCC_EL_TYPE*)(arr->data)+idx;
  }
lemma void construct_lcc_element(ARRAY_LCC_EL_TYPE *p);
requires p->n_rx_queue |-> ?nrq &*&
         0 <= nrq &*& nrq < MAX_RX_QUEUE_PER_LCORE &*&
         arrp_rq(_, &p->rx_queue_list) &*&
         arrp_u16(_, &p->tx_queue_id) &*&
         arrp_bat(_, &p->tx_mbufs) &*&
         struct_lcore_conf_padding(p);
ensures lcore_confp(_, p);

@*/

// In-place initialization
void array_lcc_init(struct ArrayLcc *arr_out);
/*@ requires chars(arr_out->data,
                   sizeof(ARRAY_LCC_EL_TYPE)*ARRAY_LCC_CAPACITY, _);@*/
/*@ ensures arrp_lcc(?lst, arr_out) &*&
            length(lst) == ARRAY_LCC_CAPACITY; @*/

ARRAY_LCC_EL_TYPE *array_lcc_begin_access(struct ArrayLcc *arr, int index);
//@ requires arrp_lcc(?lst, arr) &*& 0 <= index &*& index < ARRAY_LCC_CAPACITY;
/*@ ensures arrp_lcc_acc(lst, arr, index) &*&
            result == arrp_the_missing_cell_lcc(arr, index) &*&
            lcore_confp(nth(index, lst), result) &*&
            nth(index, lst) == lcore_confi(2);
  @*/

void array_lcc_end_access(struct ArrayLcc *arr);
/*@ requires arrp_lcc_acc(?lst, arr, ?idx) &*&
             lcore_confp(?lc, arrp_the_missing_cell_lcc(arr, idx)) &*&
             lc == lcore_confi(2); @*/
/*@ ensures arrp_lcc(update(idx, lc, lst), arr) &*&
            length(update(idx, lc, lst)) == ARRAY_LCC_CAPACITY; @*/

#endif//_ARRAY_LCC_H_INCLUDED_
