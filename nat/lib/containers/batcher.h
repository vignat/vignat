#ifndef _BATCHER_H_INCLUDED_
#define _BATCHER_H_INCLUDED_

#include "lib/static-component-params.h"

#ifndef BATCHER_EL_TYPE
#  error "Must define the batcher element type."
#endif//BATCHER_EL_TYPE

#ifndef BATCHER_CAPACITY
#  error "Must define the batcher capacity."
#endif// BATCHER_CAPACITY

struct Batcher
{
  BATCHER_EL_TYPE batch[BATCHER_CAPACITY];
  int len;
};


// In-place initialization.
void batcher_init(struct Batcher* bat_out);
void batcher_push(struct Batcher *bat, BATCHER_EL_TYPE val);
void batcher_access_all(struct Batcher *bat,
                        BATCHER_EL_TYPE **vals_out, int *count_out);
void batcher_clear(struct Batcher *bat);

int batcher_full(struct Batcher *bat);
int batcher_empty(struct Batcher *bat);


#endif//_BATCHER_H_INCLUDED_
