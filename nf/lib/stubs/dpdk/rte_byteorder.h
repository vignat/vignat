#pragma once


inline uint16_t
rte_cpu_to_be_16(uint16_t x)
{
	return ((x & 0xFF) << 16) | (x >> 16);
}
