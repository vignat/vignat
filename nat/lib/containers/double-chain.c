#include <stdlib.h>
#include <string.h>

#include "double-chain.h"
#include "double-chain-impl.h"

//@ #include "arith.gh"

struct DoubleChain {
  struct dchain_cell* cells;
  uint32_t *timestamps;
};

/*@

  predicate double_chainp(dchain ch,
                          struct DoubleChain* cp) =
    true;
  @*/

int dchain_allocate(int index_range, struct DoubleChain** chain_out)
  /*@ requires *chain_out |-> ?old_val &*&
               0 < index_range &*& index_range <= IRANG_LIMIT; @*/
  /*@ ensures result == 0 ?
   *chain_out |-> old_val :
   (result == 1 &*& *chain_out |-> ?chp &*&
   double_chainp(empty_dchain_fp(index_range), chp));
   @*/
{

  struct DoubleChain* old_chain_out = *chain_out;
  struct DoubleChain* chain_alloc = malloc(sizeof(struct DoubleChain));
  if (chain_alloc == NULL) return 0;
  *chain_out = (struct DoubleChain*) chain_alloc;

  //@ dcell_layout_assumptions((*chain_out)->cells);

  /*@
    mul_bounds(sizeof (struct dchain_cell), 1024,
               (index_range + DCHAIN_RESERVED), IRANG_LIMIT + DCHAIN_RESERVED);
    @*/
  struct dchain_cell* cells_alloc =
    malloc(sizeof (struct dchain_cell)*(index_range + DCHAIN_RESERVED));
  if (cells_alloc == NULL) {
    free(chain_alloc);
    *chain_out = old_chain_out;
    return 0;
  }
  (*chain_out)->cells = cells_alloc;

  uint32_t* timestamps_alloc = malloc(sizeof(uint32_t)*(index_range));
  if (timestamps_alloc == NULL) {
    free((void*)cells_alloc);
    free(chain_alloc);
    *chain_out = old_chain_out;
    return 0;
  }

  dchain_impl_init((*chain_out)->cells, index_range);
  return 1;
}

int dchain_allocate_new_index(struct DoubleChain* chain,
                              int *index_out, uint32_t time)
  /*@ requires double_chainp(?ch, chain) &*& *index_out |-> ?i; @*/
  /*@ ensures dchain_out_of_space_fp(ch) ?
    (result == 0 &*& *index_out |-> i &*&
    double_chainp(ch, chain)) :
    (result == 1 &*& *index_out |-> ?in &*&
    false == dchain_allocated_fp(ch, in) &*&
    0 <= in &*& in < dchain_index_range_fp(ch) &*&
    double_chainp(dchain_allocate_fp(ch, in, time), chain)); @*/
{
  int ret = dchain_impl_allocate_new_index(chain->cells, index_out);
  if (ret) chain->timestamps[*index_out] = time;
  return ret;
}

int dchain_rejuvenate_index(struct DoubleChain* chain,
                            int index, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
  0 <= index &*& index < dchain_index_range_fp(ch); @*/
/*@ ensures dchain_allocated_fp(ch, index) ?
  (result == 1 &*&
  double_chainp(dchain_rejuvenate_fp(ch, index, time), chain)) :
  (result == 0 &*&
  double_chainp(ch, chain)); @*/
{
  int ret = dchain_impl_rejuvenate_index(chain->cells, index);
  if (ret) {
    if (chain->timestamps[index] > time) return 0;
    chain->timestamps[index] = time;
  }
  return ret;
}

int dchain_expire_one_index(struct DoubleChain* chain,
                            int* index_out, uint32_t time)
/*@ requires double_chainp(?ch, chain) &*&
 *index_out |-> ?io; @*/
/*@ ensures (dchain_is_empty_fp(ch) ?
  (double_chainp(ch, chain) &*&
  *index_out |-> io &*&
  result == 0) :
  (dchain_get_oldest_time_fp(ch) < time ?
  (*index_out |-> ?oi &*&
  dchain_get_oldest_index_fp(ch) == oi &*&
  double_chainp(dchain_remove_index_fp(ch, oi), chain) &*&
  result == 1) :
  (double_chainp(ch, chain) &*&
  *index_out |-> io &*&
  result == 0))); @*/
{
  int has_ind = dchain_impl_get_oldest_index(chain->cells, index_out);
  if (has_ind) {
    if (chain->timestamps[*index_out] < time) {
      return dchain_impl_free_index(chain->cells, *index_out);
    }
  }
  return 0;
}
