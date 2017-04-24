#ifndef _BRIDGE_LOOP_H_INCLUDED_
#define _BRIDGE_LOOP_H_INCLUDED_
#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"

/*@
  predicate bridge_loop_invariant(struct DoubleChain* dyn_heap,
                                  struct Map* dyn_map,
                                  struct Vector* dyn_vec,
                                  struct Map* st_map,
                                  struct Vector* st_vec,
                                  uint32_t capacity);
  @*/

void bridge_loop_invariant_consume(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_vec,
                                   struct Map** st_map,
                                   struct Vector** st_vec,
                                   uint32_t capacity);
/*@ requires *dyn_heap |-> ?dh &*&
             *dyn_map |-> ?dm &*&
             *dyn_vec |-> ?dv &*&
             *st_map |-> ?sm &*&
             *st_vec |-> ?sv &*&
             bridge_loop_invariant(dh, dm, dv, sm, sv, capacity); @*/
/*@ ensures *dyn_heap |-> dh &*&
            *dyn_map |-> dm &*&
            *dyn_vec |-> dv &*&
            *st_map |-> sm &*&
            *st_vec |-> sv; @*/


void bridge_loop_invariant_produce(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_vec,
                                   struct Map** st_map,
                                   struct Vector** st_vec,
                                   uint32_t capacity);
/*@ requires *dyn_heap |-> ?dh &*&
             *dyn_map |-> ?dm &*&
             *dyn_vec |-> ?dv &*&
             *st_map |-> ?sm &*&
             *st_vec |-> ?sv; @*/
/*@ ensures *dyn_heap |-> dh &*&
            *dyn_map |-> dm &*&
            *dyn_vec |-> dv &*&
            *st_map |-> sm &*&
            *st_vec |-> sv &*&
            bridge_loop_invariant(dh, dm, dv, sm, sv, capacity); @*/

void bridge_loop_iteration_begin(struct DoubleChain** dyn_heap,
                                 struct Map** dyn_map,
                                 struct Vector** dyn_vec,
                                 struct Map** st_map,
                                 struct Vector** st_vec,
                                 uint32_t capacity);
/*@ requires true; @*/
/*@ ensures true; @*/

void bridge_loop_iteration_end(struct DoubleChain** dyn_heap,
                               struct Map** dyn_map,
                               struct Vector** dyn_vec,
                               struct Map** st_map,
                               struct Vector** st_vec,
                               uint32_t capacity);
/*@ requires true; @*/
/*@ ensures true; @*/

void bridge_loop_iteration_assumptions(struct DoubleChain** dyn_heap,
                                       struct Map** dyn_map,
                                       struct Vector** dyn_vec,
                                       struct Map** st_map,
                                       struct Vector** st_vec,
                                       uint32_t capacity);
/*@ requires true; @*/
/*@ ensures true; @*/

#endif//_BRIDGE_LOOP_H_INCLUDED_
