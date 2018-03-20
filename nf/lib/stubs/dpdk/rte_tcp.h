// used with VeriFast, no pragma
#ifndef RTE_TCP_H
#define RTE_TCP_H

#include <stdint.h>


struct tcp_hdr {
	uint16_t src_port;
	uint16_t dst_port;
	uint32_t sent_seq;
	uint32_t recv_ack;
	uint8_t  data_off;
	uint8_t  tcp_flags;
	uint16_t rx_win;
	uint16_t cksum;
	uint16_t tcp_urp;
};

#endif
