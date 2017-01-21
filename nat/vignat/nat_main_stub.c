#include <inttypes.h>

#include <klee/klee.h>
#include "lib/stubs/loop.h"
#include "lib/stubs/my-time-stub-control.h"
#include "lib/stubs/rte_stubs.h"

#include "lib/flowmanager.h"

#include "../nat_config.h"
#include "../nat_forward.h"
#include "../nat_log.h"
#include "../nat_time.h"


struct str_field_descr mbuf_descrs[] = {
  //Do not forget about "buf_addr" -- it is a pointer that is why it is not listed here.
  {offsetof(struct rte_mbuf, buf_physaddr), sizeof(uint64_t), "buf_physaddr"},
  {offsetof(struct rte_mbuf, buf_len), sizeof(uint16_t), "buf_len"},
  {offsetof(struct rte_mbuf, data_off), sizeof(uint16_t), "data_off"},
  {offsetof(struct rte_mbuf, refcnt), sizeof(uint16_t), "refcnt"},
  {offsetof(struct rte_mbuf, nb_segs), sizeof(uint8_t), "nb_segs"},
  {offsetof(struct rte_mbuf, port), sizeof(uint8_t), "port"},
  {offsetof(struct rte_mbuf, ol_flags), sizeof(uint64_t), "ol_flags"},
  {offsetof(struct rte_mbuf, packet_type), sizeof(uint32_t), "packet_type"},
  {offsetof(struct rte_mbuf, pkt_len), sizeof(uint32_t), "pkt_len"},
  {offsetof(struct rte_mbuf, data_len), sizeof(uint16_t), "data_len"},
  {offsetof(struct rte_mbuf, vlan_tci), sizeof(uint16_t), "vlan_tci"},
  {offsetof(struct rte_mbuf, hash), sizeof(uint32_t), "hash"},
  {offsetof(struct rte_mbuf, seqn), sizeof(uint32_t), "seqn"},
  {offsetof(struct rte_mbuf, vlan_tci_outer), sizeof(uint16_t), "vlan_tci_outer"},
  {offsetof(struct rte_mbuf, udata64), sizeof(uint64_t), "udata64"},
  {offsetof(struct rte_mbuf, pool), sizeof(void*), "pool"},
  {offsetof(struct rte_mbuf, next), sizeof(struct rte_mbuf*), "next"},
  {offsetof(struct rte_mbuf, tx_offload), sizeof(uint64_t), "tx_offload"},
  {offsetof(struct rte_mbuf, priv_size), sizeof(uint16_t), "priv_size"},
  {offsetof(struct rte_mbuf, timesync), sizeof(uint16_t), "timesync"},
};

struct nested_field_descr user_buf_nested[] = {
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, version_ihl), sizeof(uint8_t), "version_ihl"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, type_of_service), sizeof(uint8_t), "type_of_service"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, total_length), sizeof(uint16_t), "total_length"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, packet_id), sizeof(uint16_t), "packet_id"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, fragment_offset), sizeof(uint16_t), "fragment_offset"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, time_to_live), sizeof(uint8_t), "time_to_live"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, next_proto_id), sizeof(uint8_t), "next_proto_id"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, hdr_checksum),
    sizeof(uint16_t), "hdr_checksum"},
  */
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, src_addr), sizeof(uint32_t), "src_addr"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, dst_addr), sizeof(uint32_t), "dst_addr"},

  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, sent_seq), sizeof(uint32_t), "sent_seq"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, recv_ack), sizeof(uint32_t), "recv_ack"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, data_off), sizeof(uint8_t), "data_off"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, tcp_flags), sizeof(uint8_t), "tcp_flags"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, rx_win), sizeof(uint16_t), "rx_win"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, cksum),
    sizeof(uint16_t), "cksum"},
  */
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, tcp_urp), sizeof(uint16_t), "tcp_urp"},
};

#define KLEE_TRACE_MBUF(m_ptr)                                          \
  klee_trace_param_ptr(m_ptr, sizeof(*m_ptr), #m_ptr);                  \
  klee_trace_param_ptr_field(m_ptr, offsetof(struct rte_mbuf, buf_addr), \
                             sizeof(struct user_buf*), "buf_addr");     \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) { \
    klee_trace_param_ptr_field(m_ptr,                                   \
                               mbuf_descrs[i].offset,                   \
                               mbuf_descrs[i].width,                    \
                               mbuf_descrs[i].name);                    \
  }                                                                     \
  klee_trace_extra_ptr(m_ptr->buf_addr, sizeof(struct user_buf), "user_buf_addr"); \
  klee_trace_extra_ptr_field(m_ptr->buf_addr, offsetof(struct user_buf, ether), \
                             sizeof(struct ether_hdr), "ether");        \
  klee_trace_extra_ptr_field(m_ptr->buf_addr, offsetof(struct user_buf, ipv4), \
                             sizeof(struct ipv4_hdr), "ipv4");          \
  klee_trace_extra_ptr_field(m_ptr->buf_addr, offsetof(struct user_buf, tcp), \
                             sizeof(struct tcp_hdr), "tcp");            \
  klee_trace_extra_ptr_nested_field(m_ptr->buf_addr,                    \
                                    offsetof(struct user_buf, ether),   \
                                    offsetof(struct ether_hdr, ether_type), \
                                    sizeof(uint16_t), "ether_type");    \
  for (int i = 0; i < sizeof(user_buf_nested)/sizeof(user_buf_nested[0]); ++i) {\
    klee_trace_extra_ptr_nested_field(m_ptr->buf_addr,                  \
                                      user_buf_nested[i].base_offset,   \
                                      user_buf_nested[i].offset,        \
                                      user_buf_nested[i].width,         \
                                      user_buf_nested[i].name);         \
  }

// " <-- work around a bug in nano with string syntax coloring caused by the macro above

static void
received_packet(uint8_t device, struct rte_mbuf* mbuf)
{
	klee_trace_ret();
	klee_trace_param_i32(device, "received_packet_device");
	KLEE_TRACE_MBUF(mbuf);
}


static void
lcore_main(struct nat_config* config)
{
	nat_core_init(config);

	uint32_t starting_time = start_time();

	int x = klee_int("loop_termination");
	unsigned lcore_id = rte_lcore_id(); // TODO do we need that?

	loop_iteration_begin(get_dmap_pp(), get_dchain_pp(), lcore_id, starting_time, config->max_flows, config->start_port);

	while (klee_induce_invariants() & x) {
		loop_iteration_assumptions(get_dmap_pp(), get_dchain_pp(), lcore_id, starting_time, config->max_flows, config->start_port);

		uint32_t now = current_time();
		uint8_t device = klee_range(0, RTE_MAX_ETHPORTS, "device");
		struct rte_mbuf* pkts_burst[1];
		uint16_t nb_rx = rte_eth_rx_burst(device, 0, pkts_burst, 1);

		if (0 < nb_rx) {
			received_packet(device, pkts_burst[0]);

			nat_core_process(config, device, pkts_burst[0], now);
		}

		loop_iteration_end(get_dmap_pp(), get_dchain_pp(), lcore_id, now, config->max_flows, config->start_port);
	}
}


int
main(int argc, char* argv[])
{
	// Initialize the Environment Abstraction Layer (EAL)
	int ret = rte_eal_init(argc, argv);
	if (ret < 0) {
		rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
	}
	argc -= ret;
	argv += ret;

	// Initialize the config
	struct nat_config config;
	nat_config_init(&config, argc, argv);

	// Run!
	lcore_main(&config);

	return 0;
}
