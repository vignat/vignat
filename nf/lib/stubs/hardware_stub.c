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

// TODO some check at each delay that read-only bits are not changed

static void
stub_device_init(struct stub_device dev)
{
	// "Fake" memory, intercepted
	dev.mem = malloc(dev.mem_len);
	klee_intercept_reads(dev.mem, "stub_hardware_read");
	klee_intercept_writes(dev.mem, "stub_hardware_write");

	// Real backing store
	dev.mem_shadow = malloc(dev.mem_len);
	memset(dev.mem_shadow, 0, dev.mem_len);

#define SET(addr, val) *((uint32_t*) (dev.mem_shadow + addr)) = val;

	// page 544
	// Device Status Register — STATUS (0x00008; RO)

	// 0-1: Reserved (00)
	// 2-3: Lan ID (00 - Lan 0 / 01 - Lan 1)
	// 4-6: Reserved (00)
	// 7: Linkup Status Indication (0 - ???)
	// 8-9: Reserved (00)
	// 10-17: Num VFs (0 - no VFs; note: "Bit 17 is always 0b")
	// 18: IO Active (0 - not active; note: "reflects the value of the VF Enable (VFE) bit in the IOV Control/Status register")
	// 19: Status (0 - not issuing any master requests)
	// 20-31: Reserved (0x00)
	SET(0x00008, 0b00000000000000000000000000000000);


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
	// 22-31: Reserved (0x0)
	SET(0x10010, 0b00000000000000000001011100110000);


	// page 565
	// Function Active and Power State to Manageability — FACTPS (0x10150; RO)

	// 0-1: Power state indication of function 0 (00 - DR)
	// 2: Lan 0 Enable (1 - enabled)
	// 3: Function 0 Auxiliary Power PM Enable (0 - ???)
	// 4-5: Reserved (00)
	// 6-7: Power state indication of function 1 (00 - disabled)
	// 8: Lan 1 Enable (0 - disabled)
	// 9: Function 1 Auxiliary Power PM Enable (0 - disabled)
	// 10-28: Reserved (0x0)
	// 29: Manageability Clock Gated (0 - not gated)
	// 30: LAN Function Sel (0 - not inverted) TODO enable
	// 31: PM State Changed (0 - not changed)
	SET(0x10150, 0b00000000000000000000000000000100);


	// pages 567-568
	// Firmware Semaphore Register — FWSM (0x10148; RW)
	// "This register should be written only by the manageability firmware.
	//  The device driver should only read this register."

	// 0: Firmware semaphore (0 - not accessing)
	// 1-3: Firmware mode (000 - none, manageability off)
	// 4-5: Reserved (00)
	// 6: EEPROM Reloaded Indication (1 - has been reloaded)
	// 7-14: Reserved (0x0)
	// 15: Firmware Valid Bit (1 - ready, boot has finished) TODO make it 0
	// 16-18: Reset Counter (000 - not reset)
	// 19-24: External Error Indication (0x00 - No error)
	// 25: PCIe Configuration Error Indication (0 - no error)
	// 26: PHY/SERDES0 Configuration Error Indication (0 - no error, LAN0 is fine)
	// 27: PHY/SERDES1 Configuration Error Indication (0 - no error, LAN1 is fine)
	// 28-31: Reserved (0000)
	SET(0x10148, 0b00000000000000001000000001000000);
}

static struct stub_device
stub_device_get(uint64_t addr)
{
	for (int n = 0; n < sizeof(DEVICES)/sizeof(DEVICES[0]); n++) {
		if (addr == (uint64_t) DEVICES[n].mem) {
			return DEVICES[n];
		}
	}

	klee_abort();
}

uint64_t
stub_hardware_read(uint64_t addr, unsigned offset, unsigned size)
{
klee_print_expr("READ", addr);
klee_print_expr("off", offset);
klee_print_expr("size", size);

	struct stub_device dev = stub_device_get(addr);

	if (size == 1) {
		return *((uint8_t*) (dev.mem_shadow + offset));
	}
	if (size == 2) {
		return *((uint16_t*) (dev.mem_shadow + offset));
	}
	if (size == 4) {
		return *((uint32_t*) (dev.mem_shadow + offset));
	}
	if (size == 8) {
		return *((uint64_t*) (dev.mem_shadow + offset));
	}

	klee_abort();
}

void
stub_hardware_write(uint64_t addr, unsigned offset, unsigned size, uint64_t value)
{
klee_print_expr("WRITE", addr);
klee_print_expr("off", offset);
klee_print_expr("size", size);
klee_print_expr("value", value);

	struct stub_device dev = stub_device_get(addr);

	if (size == 1) {
		*((uint8_t*) (dev.mem_shadow + offset)) = (uint8_t) value;
	} else if (size == 2) {
		*((uint16_t*) (dev.mem_shadow + offset)) = (uint16_t) value;
	} else if (size == 4) {
		*((uint32_t*) (dev.mem_shadow + offset)) = (uint32_t) value;
	} else if (size == 8) {
		*((uint64_t*) (dev.mem_shadow + offset)) = (uint64_t) value;
	} else {
		klee_abort();
	}
}


__attribute__((constructor(101))) // Low prio, must execute before other stuff
static void
stub_hardware_init(void)
{
	// Helper method declarations
	char* stub_pci_name(int index);

	// Device initialization
	for (int n = 0; n < sizeof(DEVICES)/sizeof(DEVICES[0]); n++) {
		struct stub_device stub_dev = {
			.name = stub_pci_name(n),
			.mem = NULL,
			.mem_len = 1 << 20, // 2^20 bytes
			.mem_shadow = NULL
		};
		stub_device_init(stub_dev);
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

