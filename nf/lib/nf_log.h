#pragma once

#include <stdio.h>

#define NF_INFO(text, ...) printf(text "\n", ##__VA_ARGS__); fflush(stdout);

#if ENABLE_LOG
	#define NF_DEBUG(text, ...) fprintf(stderr, "DEBUG: " text "\n", ##__VA_ARGS__); fflush(stderr);
#else
	#define NF_DEBUG(...)
#endif
