#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

//@ #include "lib/predicates.gh"

void loop_invariant_consume();
//@ requires evproc_loop_invariant();
//@ ensures true;

void loop_invariant_produce();
//@ requires true;
//@ ensures evproc_loop_invariant();

void loop_iteration_begin();

void loop_iteration_end();

void loop_enumeration_begin(int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end();
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
