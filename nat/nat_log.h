#pragma once

#if KLEE_VERIFICATION
	#define NAT_INFO(...)
	#define NAT_DEBUG(...)
#else
	#include <stdio.h>

	#define NAT_INFO(text, ...) printf(text "\n", ##__VA_ARGS__); fflush(stdout);

	#if ENABLE_LOG
		#define NAT_DEBUG(text, ...) printf("DEBUG: " text "\n", ##__VA_ARGS__); fflush(stdout);
	#else
		#define NAT_DEBUG(...)
	#endif
#endif
