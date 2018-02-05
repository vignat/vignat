#pragma once

#include <stddef.h>


struct stub_device {
	char* name;
	void* mem;
	size_t mem_len;
};

struct stub_device DEVICES[2];
