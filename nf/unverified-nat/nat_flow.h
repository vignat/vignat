#pragma once

#include <inttypes.h>
#include <string.h>


struct nat_flow_id {
	uint32_t src_addr;
	uint16_t src_port;
	uint32_t dst_addr;
	uint16_t dst_port;
	// To use DPDK maps, this type must have a power of 2 size,
	// so we make this 32-bit even though it only needs 8
	uint32_t protocol;
} __attribute__((__packed__));

static uint64_t
nat_flow_id_hash(struct nat_flow_id id)
{
	uint64_t hash = 17;
	hash = hash * 31 + id.src_addr;
	hash = hash * 31 + id.src_port;
	hash = hash * 31 + id.dst_addr;
	hash = hash * 31 + id.dst_port;
	hash = hash * 31 + id.protocol;
	return hash;
}

static bool
nat_flow_id_eq(struct nat_flow_id left, struct nat_flow_id right)
{
	return 1 - memcmp(&left, &right, sizeof(struct nat_flow_id));
}


struct nat_flow {
	struct nat_flow_id id;
	uint8_t internal_device;
	uint16_t external_port;
	uint32_t last_packet_timestamp;
};
