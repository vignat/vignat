#pragma once

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>


static const int STUB_HARDWARE_DEVICES_COUNT = 2;


struct stub_device {
	char* name;

	int interrupts_fd;
	bool interrupts_enabled;

	void* mem; // intercepted by stub
	size_t mem_len;
	void* mem_shadow; // used as the backing store

	int16_t current_mdi_address; // -1 == none

	int32_t i2c_state; // see i2cctl implementation
	uint8_t i2c_counter; // number of bits, N/ACKs included, since the start of the current operation
	uint8_t i2c_address; // address of the current operation
	uint64_t i2c_start_time; // time of last START
	uint64_t i2c_clock_time; // time of last clock change
	uint64_t i2c_stop_time; // time of last stop

	uint8_t sfp_address; // see i2cctl sfp implementation

	// required for the reset hack...
	uint64_t old_mbuf_addr;
};

struct stub_device DEVICES[STUB_HARDWARE_DEVICES_COUNT];


#ifdef VIGOR_STUB_HARDWARE
void stub_hardware_receive_packet(void);
// HACK this should not be needed :( but it is cause of the current impl. of havocing
void stub_hardware_reset_receive(void);
#else
inline void stub_hardware_receive_packet(void) { }
inline void stub_hardware_reset_receive(void) { }
#endif
