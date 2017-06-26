#pragma once

#if KLEE_VERIFICATION
	#define NF_INFO(...)
	#define NF_DEBUG(...)
#else
	#include <stdio.h>

	#define NF_INFO(text, ...) printf(text "\n", ##__VA_ARGS__); fflush(stdout);

	#if ENABLE_LOG
		#define NF_DEBUG(text, ...) printf("DEBUG: " text "\n", ##__VA_ARGS__); fflush(stdout);
	#else
		#define NF_DEBUG(...)
	#endif
#endif
