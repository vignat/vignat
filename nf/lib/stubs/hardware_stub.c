#include "lib/stubs/hardware_stub.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rte_cycles.h" // to include the next one cleanly
#include "generic/rte_cycles.h" // for rte_delay_us_callback_register

#include <klee/klee.h>


static void
stub_delay_us(unsigned int us)
{
klee_print_expr("DELAY", us);
}


__attribute__((constructor(101))) // Low prio, must execute before other stuff
static void
stub_hardware_init(void)
{
	// Helper method declarations
	char* stub_pci_name(int index);

	// Device initialization
	for (int n = 0; n < sizeof(DEVICES)/sizeof(DEVICES[0]); n++) {
		char* dev = stub_pci_name(n);
		size_t mem_len = 1 << 20; // 2^20 bytes
		void* mem = malloc(mem_len);
		memset(mem, 0, mem_len);

klee_print_expr("DEVICE", n);klee_print_expr("start",mem);

		struct stub_device stub_dev = {
			.name = dev,
			.mem = mem,
			.mem_len = mem_len
		};
		DEVICES[n] = stub_dev;
	}

	// DPDK "delay" method override
	rte_delay_us_callback_register(stub_delay_us);
}

// Helper methods - not part of the stubs

char*
stub_pci_name(int index)
{
	klee_assert(index >= 0 && index < 10); // simpler

	char buffer[1024];
	snprintf(buffer, sizeof(buffer), "0000:00:00.%d", index);
	return strdup(buffer);
}

