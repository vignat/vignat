#include "batcher.h"

void batcher_init(struct Batcher* bat_out)
{
  bat_out->len = 0;
}

void batcher_push(struct Batcher *bat, BATCHER_EL_TYPE val)
{
  bat->batch[bat->len] = val;
  ++bat->len;
}

void batcher_access_all(struct Batcher *bat,
                        BATCHER_EL_TYPE **vals_out, int *count_out)
{
  *vals_out = bat->batch;
  *count_out = bat->len;
}

void batcher_clear(struct Batcher *bat)
{
  bat->len = 0;
}

int batcher_full(struct Batcher *bat)
{
  return (BATCHER_CAPACITY - 1) <= bat->len;
}

int batcher_empty(struct Batcher *bat)
{
  return bat->len <= 0;
}
