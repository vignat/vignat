#pragma once

#include <stddef.h>


#ifdef ENABLE_HARDWARE_STUB
static const int DEVICES_COUNT = 2;
#else
static const int DEVICES_COUNT = 0;
#endif


struct stub_device {
	char* name;
	void* mem;
	size_t mem_len;
};

struct stub_device DEVICES[DEVICES_COUNT];
