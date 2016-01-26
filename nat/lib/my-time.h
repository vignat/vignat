#ifndef _MY_TIME_H_INCLUDED_
#define _MY_TIME_H_INCLUDED_

#include <stdint.h>

//@ #include "lib/predicates.gh"

uint32_t current_time(void);
//@ requires last_time(?x);
//@ ensures x <= result &*& last_time(result);

#endif //_MY_TIME_H_INCLUDED_
