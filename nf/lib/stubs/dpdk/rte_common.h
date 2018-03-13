#pragma once

#include <klee/klee.h>


static inline void
rte_exit(int exit_code, const char * format,  ...)
{
	klee_silent_exit(exit_code);
}
