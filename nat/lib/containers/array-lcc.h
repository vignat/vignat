#ifndef _ARRAY_LCC_H_INCLUDED_
#define _ARRAY_LCC_H_INCLUDED_

#include <stdint.h>
#include "lib/ignore.h"
#include "lib/static-component-params.h"
#include "lib/containers/array-rq.h"
#include "lib/containers/array-u16.h"
#include "lib/containers/array-bat.h"

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
  predicate pure_lcore_confp(lcore_confi lc, struct lcore_conf *lcp);
  predicate lcore_confp(lcore_confi lc, struct lcore_conf *lcp) =
      pure_lcore_confp(lc, lcp) &*&
      arrp_rq(_, &lcp->rx_queue_list) &*&
      arrp_u16(_, &lcp->tx_queue_id);
  predicate some_lcore_confp(struct lcore_conf *lcp) = lcore_confp(_, lcp);
  @*/

/*@
//params: lcore_confi, lcore_confp
predicate arrp_lcc(list<lcore_confi> data, struct ArrayLcc *arr);
predicate arrp_lcc_acc(list<lcore_confi> data, struct ArrayLcc *arr,
                       int idx);
fixpoint ARRAY_LCC_EL_TYPE *arrp_the_missing_cell_lcc(struct ArrayLcc *arr,
                                                      int idx);
lemma void construct_lcc_element(ARRAY_LCC_EL_TYPE *p);
requires p->n_rx_queue |-> ?nrq &*&
         0 < nrq &*& nrq < MAX_RX_QUEUE_PER_LCORE &*&
         chars((char*)(p->rx_queue_list.data), 16*sizeof(struct lcore_rx_queue), _) &*&
         struct_ArrayRq_padding(&p->rx_queue_list) &*&
         ushorts((unsigned short*)(p->tx_queue_id.data), 32, _) &*&
         struct_ArrayU16_padding(&p->tx_queue_id) &*&
         chars((char*)p->tx_mbufs.data, 32*sizeof(struct Batcher), _) &*&
         struct_ArrayBat_padding(&p->tx_mbufs) &*&
         struct_lcore_conf_padding(p);
ensures lcore_confp(_, p);

@*/

#endif//_ARRAY_LCC_H_INCLUDED_
