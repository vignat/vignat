#ifndef _MY_TIME_STUB_CONTROL_H_INCLUDED_
#define _MY_TIME_STUB_CONTROL_H_INCLUDED_

#include <stdint.h>

//@ #include "lib/predicates.gh"

uint32_t start_time(void);
//@ requires true;
//@ ensures last_time(result);

uint32_t restart_time(void);

uint32_t get_start_time(void);

#endif //_MY_TIME_STUB_CONTROL_H_INCLUDED_
