#include "lib/stubs/hardware_stub.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rte_cycles.h" // to include the next one cleanly
#include "generic/rte_cycles.h" // for rte_delay_us_callback_register

#include <klee/klee.h>


// All citations here refer to https://www.intel.com/content/dam/www/public/us/en/documents/datasheets/82599-10-gbe-controller-datasheet.pdf


static void
stub_delay_us(unsigned int us)
{
klee_print_expr("DELAY", us);
}

static void
stub_memory_init(void* mem)
{
	// page 552
	// EEPROM/Flash Control Register — EEC (0x10010; RW)
	// 0: Clock input (0 - not enabled)
	// 1: Chip select (0 - not enabled)
	// 2: Data input (0 - not enabled)
	// 3: Data output (X - don't care)
	// 4-5: Flash Write Enable Control (11 - not allowed)
	// 6: Request EEPROM Access (0 - not enabled)
	// 7: Grant EEPROM Access (0 - not enabled)
	// 8: EEPROM Present (1 - present, correct signature)
	// 9: EEPROM Auto-Read Done (1 - done, since we fake hardware...)
	// 10: Reservee (1 - Reserved)
	// 11-14: EEPROM Size (0100 - Default)
	// 15: PCIe Analog Done (0 - not done)
	// 16: PCIe Core Done (0 - not done)
	// 17: PCIe General Done (0 - not done)
	// 18: PCIe Function Done (0 - not done)
	// 19: Core Done (0 - not done)
	// 20: Core CSR Done (0 - not done)
	// 21: MAC Done (0 - not done)
	// 22-31: Reserved (0x0 - reads as 0b)
	((uint32_t*) mem)[0x10010] = 0b00000000000000000001011100110000;
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
		size_t mem_len = 1 << 20; // 2^20 bytes - should be enough
		void* mem = malloc(mem_len);
		memset(mem, 0, mem_len);

klee_print_expr("DEVICE", n);klee_print_expr("start",mem);

		struct stub_device stub_dev = {
			.name = dev,
			.mem = mem,
			.mem_len = mem_len
		};
		DEVICES[n] = stub_dev;

		stub_memory_init(mem);
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

