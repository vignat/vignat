#pragma once

#include <stddef.h>


#ifdef ENABLE_HARDWARE_STUB
static const int DEVICES_COUNT = 2;
#else
static const int DEVICES_COUNT = 0;
#endif


struct stub_device {
	char* name;
	void* mem; // intercepted by stubs
	size_t mem_len;
	void* mem_shadow; // used as the backing store
};

struct stub_device DEVICES[DEVICES_COUNT];
