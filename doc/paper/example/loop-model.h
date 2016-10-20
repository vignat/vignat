#ifndef _LOOP_MODEL_H_INCLUDED_
#define _LOOP_MODEL_H_INCLUDED_

#include "ring.h"

void loop_invariant_consume(struct ring **r);
void loop_invariant_produce(struct ring **r);

void loop_iteration_begin(struct ring **r);
void loop_iteration_end(struct ring **r);


#endif//_LOOP_MODEL_H_INCLUDED_
