#include <time.h>
#include "nf_time.h"

uint32_t current_time(void)
//@ requires last_time(?x);
//@ ensures x <= result &*& last_time(result);
{
  // see https://github.com/verifast/verifast/issues/35
  return time(NULL);
}
