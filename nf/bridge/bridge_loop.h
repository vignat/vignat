#ifndef _BRIDGE_LOOP_H_INCLUDED_
#define _BRIDGE_LOOP_H_INCLUDED_
#include "lib/containers/double-chain.h"
#include "lib/containers/map.h"
#include "lib/containers/vector.h"
#include "bridge_data.h"
#include "lib/coherence.h"
//@ #include "lib/predicates.gh"

/*@
  predicate bridge_loop_invariant(struct DoubleChain* dyn_heap,
                                  struct Map* dyn_map,
                                  struct Vector* dyn_vec,
                                  struct Map* st_map,
                                  struct Vector* st_vec,
                                  uint32_t capacity,
                                  uint32_t time) =
    double_chainp(?dh, dyn_heap) &*&
    mapp<ether_addri>(dyn_map, _, _, mapc(capacity, ?dm)) &*&
    vectorp<dynenti>(dyn_vec, _, ?dv) &*&
    mapp<stat_keyi>(st_map, _, _, _) &*&
    vectorp<stat_keyi>(st_vec, _, _) &*&
    map_vec_chain_coherent<ether_addri, dynenti>(dm, dv, dh) &*&
    last_time(time);
  @*/

void bridge_loop_invariant_consume(struct DoubleChain** dyn_heap,
                                   struct Map** dyn_map,
                                   struct Vector** dyn_vec,
                                   struct Map** st_map,
                                   struct Vector** st_vec,
                                   uint32_t capacity,
                                   uint32_t time);
/*@ requires *dyn_heap |-> ?dh &*&
             *dyn_map |-> ?dm &*&
             *dyn_vec |-> ?dv &*&
             *st_map |-> ?sm &*&
             *st_vec |-> ?sv &*&
             bridge_loop_invariant(dh, dm, dv, sm, sv, capacity, time); @*/
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
                                   uint32_t capacity,
                                   uint32_t* time);
/*@ requires *dyn_heap |-> ?dh &*&
             *dyn_map |-> ?dm &*&
             *dyn_vec |-> ?dv &*&
             *st_map |-> ?sm &*&
             *st_vec |-> ?sv &*&
             *time |-> _; @*/
/*@ ensures *dyn_heap |-> dh &*&
            *dyn_map |-> dm &*&
            *dyn_vec |-> dv &*&
            *st_map |-> sm &*&
            *st_vec |-> sv &*&
            *time |-> ?t &*&
            bridge_loop_invariant(dh, dm, dv, sm, sv, capacity, t); @*/

void bridge_loop_iteration_begin(struct DoubleChain** dyn_heap,
                                 struct Map** dyn_map,
                                 struct Vector** dyn_vec,
                                 struct Map** st_map,
                                 struct Vector** st_vec,
                                 uint32_t capacity,
                                 uint32_t time);
/*@ requires true; @*/
/*@ ensures true; @*/

void bridge_loop_iteration_end(struct DoubleChain** dyn_heap,
                               struct Map** dyn_map,
                               struct Vector** dyn_vec,
                               struct Map** st_map,
                               struct Vector** st_vec,
                               uint32_t capacity, uint32_t time);
/*@ requires true; @*/
/*@ ensures true; @*/

void bridge_loop_iteration_assumptions(struct DoubleChain** dyn_heap,
                                       struct Map** dyn_map,
                                       struct Vector** dyn_vec,
                                       struct Map** st_map,
                                       struct Vector** st_vec,
                                       uint32_t capacity, uint32_t time);
/*@ requires true; @*/
/*@ ensures true; @*/

#endif//_BRIDGE_LOOP_H_INCLUDED_
