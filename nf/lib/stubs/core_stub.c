#include "lib/stubs/core_stub.h"
#include "lib/stubs/containers/str-descr.h"

#include <stdlib.h>
#include <string.h>

#include <rte_memory.h>

#include <klee/klee.h>


struct str_field_descr mbuf_descrs[] = {
  //Do not forget about "buf_addr" -- it is a pointer that is why it is not listed here.
  {offsetof(struct rte_mbuf, buf_iova), sizeof(rte_iova_t), "buf_iova"},
  {offsetof(struct rte_mbuf, data_off), sizeof(uint16_t), "data_off"},
  {offsetof(struct rte_mbuf, refcnt), sizeof(uint16_t), "refcnt"},
  {offsetof(struct rte_mbuf, nb_segs), sizeof(uint16_t), "nb_segs"},
  {offsetof(struct rte_mbuf, port), sizeof(uint16_t), "port"},
  {offsetof(struct rte_mbuf, ol_flags), sizeof(uint64_t), "ol_flags"},
  {offsetof(struct rte_mbuf, packet_type), sizeof(uint32_t), "packet_type"},
  {offsetof(struct rte_mbuf, pkt_len), sizeof(uint32_t), "pkt_len"},
  {offsetof(struct rte_mbuf, data_len), sizeof(uint16_t), "data_len"},
  {offsetof(struct rte_mbuf, vlan_tci), sizeof(uint16_t), "vlan_tci"},
  {offsetof(struct rte_mbuf, hash), sizeof(uint32_t), "hash"},
  {offsetof(struct rte_mbuf, vlan_tci_outer), sizeof(uint16_t), "vlan_tci_outer"},
  {offsetof(struct rte_mbuf, buf_len), sizeof(uint16_t), "buf_len"},
  {offsetof(struct rte_mbuf, timestamp), sizeof(uint64_t), "timestamp"},
  {offsetof(struct rte_mbuf, udata64), sizeof(uint64_t), "udata64"},
  /*{offsetof(struct rte_mbuf, pool), sizeof(rte_mempool*), "pool"}, TODO no real reason this is commented out? */
  /*{offsetof(struct rte_mbuf, next), sizeof(struct rte_mbuf*), "next"}, - we ban access to it, so let's not trace it */
  {offsetof(struct rte_mbuf, tx_offload), sizeof(uint64_t), "tx_offload"},
  {offsetof(struct rte_mbuf, priv_size), sizeof(uint16_t), "priv_size"},
  {offsetof(struct rte_mbuf, timesync), sizeof(uint16_t), "timesync"},
  {offsetof(struct rte_mbuf, seqn), sizeof(uint32_t), "seqn"},
};
struct nested_field_descr stub_mbuf_content_nested[] = {
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, ether_type), sizeof(uint16_t), "ether_type"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), sizeof(struct ether_addr), "d_addr"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), sizeof(struct ether_addr), "s_addr"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, version_ihl), sizeof(uint8_t), "version_ihl"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, type_of_service), sizeof(uint8_t), "type_of_service"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, total_length), sizeof(uint16_t), "total_length"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, packet_id), sizeof(uint16_t), "packet_id"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, fragment_offset), sizeof(uint16_t), "fragment_offset"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, time_to_live), sizeof(uint8_t), "time_to_live"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, next_proto_id), sizeof(uint8_t), "next_proto_id"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, hdr_checksum),
    sizeof(uint16_t), "hdr_checksum"},
  */
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, src_addr), sizeof(uint32_t), "src_addr"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, dst_addr), sizeof(uint32_t), "dst_addr"},

  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, sent_seq), sizeof(uint32_t), "sent_seq"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, recv_ack), sizeof(uint32_t), "recv_ack"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, data_off), sizeof(uint8_t), "data_off"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, tcp_flags), sizeof(uint8_t), "tcp_flags"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, rx_win), sizeof(uint16_t), "rx_win"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, cksum),
    sizeof(uint16_t), "cksum"},
  */
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, tcp_urp), sizeof(uint16_t), "tcp_urp"},
};
struct nested_nested_field_descr stub_mbuf_content_n2[] = {
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 0, sizeof(uint8_t), "a"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 1, sizeof(uint8_t), "b"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 2, sizeof(uint8_t), "c"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 3, sizeof(uint8_t), "d"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 4, sizeof(uint8_t), "e"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 5, sizeof(uint8_t), "f"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 0, sizeof(uint8_t), "a"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 1, sizeof(uint8_t), "b"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 2, sizeof(uint8_t), "c"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 3, sizeof(uint8_t), "d"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 4, sizeof(uint8_t), "e"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 5, sizeof(uint8_t), "f"},
};
#define KLEE_TRACE_MBUF(m_ptr, mname, dir)                                                                                             \
  klee_trace_param_ptr_directed(m_ptr, sizeof(*m_ptr), mname, dir);                                                                    \
  klee_trace_param_ptr_field_directed(m_ptr, offsetof(struct rte_mbuf, buf_addr), sizeof(struct stub_mbuf_content*), "buf_addr", dir); \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) {                                                               \
    klee_trace_param_ptr_field_directed(m_ptr,                                                                                         \
                                        mbuf_descrs[i].offset,                                                                         \
                                        mbuf_descrs[i].width,                                                                          \
                                        mbuf_descrs[i].name,                                                                           \
                                        dir);                                                                                          \
  }
#define KLEE_TRACE_MBUF_EPTR(m_ptr, pname, dir)                                                                               \
  klee_trace_extra_ptr(m_ptr, sizeof(*m_ptr), pname, "", dir);                                                                \
  klee_trace_extra_ptr_field(m_ptr, offsetof(struct rte_mbuf, buf_addr), sizeof(struct stub_mbuf_content*), "buf_addr", dir); \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) {                                                      \
    klee_trace_extra_ptr_field(m_ptr,                                                                                         \
                               mbuf_descrs[i].offset,                                                                         \
                               mbuf_descrs[i].width,                                                                          \
                               mbuf_descrs[i].name,                                                                           \
                               dir);                                                                                          \
  }
#define KLEE_TRACE_MBUF_CONTENT(u_ptr, dir)                                                                             \
  klee_trace_extra_ptr(u_ptr, sizeof(struct stub_mbuf_content), "user_buf_addr", "", dir);                              \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, ether), sizeof(struct ether_hdr), "ether", dir); \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, ipv4), sizeof(struct ipv4_hdr), "ipv4", dir);    \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, tcp), sizeof(struct tcp_hdr), "tcp", dir);       \
  for (int i = 0; i < sizeof(stub_mbuf_content_nested)/sizeof(stub_mbuf_content_nested[0]); ++i) {                      \
    klee_trace_extra_ptr_nested_field(u_ptr,                                                                            \
                                      stub_mbuf_content_nested[i].base_offset,                                          \
                                      stub_mbuf_content_nested[i].offset,                                               \
                                      stub_mbuf_content_nested[i].width,                                                \
                                      stub_mbuf_content_nested[i].name,                                                 \
                                      dir);                                                                             \
  }                                                                                                                     \
  for (int i = 0; i < sizeof(stub_mbuf_content_n2)/sizeof(stub_mbuf_content_n2[0]); ++i) {                              \
    klee_trace_extra_ptr_nested_nested_field                                                                            \
      (u_ptr,                                                                                                           \
       stub_mbuf_content_n2[i].base_base_offset,                                                                        \
       stub_mbuf_content_n2[i].base_offset,                                                                             \
       stub_mbuf_content_n2[i].offset,                                                                                  \
       stub_mbuf_content_n2[i].width,                                                                                   \
       stub_mbuf_content_n2[i].name,                                                                                    \
       dir);                                                                                                            \
  }


void
stub_core_trace_free(struct rte_mbuf* mbuf)
{
	KLEE_TRACE_MBUF(mbuf, "mbuf", TD_IN);
	KLEE_TRACE_MBUF_CONTENT(mbuf->buf_addr, TD_IN);
}

void
stub_core_trace_rx(struct rte_mbuf* mbuf)
{
	klee_trace_param_ptr_directed(mbuf, sizeof(struct rte_mbuf*), "mbuf", TD_BOTH);
	KLEE_TRACE_MBUF_EPTR(mbuf, "incoming_package", TD_OUT);
	KLEE_TRACE_MBUF_CONTENT(mbuf->buf_addr, TD_OUT);
}

void
stub_core_trace_tx(struct rte_mbuf* mbuf, uint16_t device)
{
	KLEE_TRACE_MBUF(mbuf, "mbuf", TD_IN);
	KLEE_TRACE_MBUF_CONTENT(mbuf->buf_addr, TD_IN);
	klee_trace_param_u16(device, "device");
}


bool
stub_core_mbuf_create(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufp)
{
	uint16_t priv_size = rte_pktmbuf_priv_size(pool);
	uint16_t mbuf_size = sizeof(struct rte_mbuf) + priv_size;
	uint16_t buf_len = rte_pktmbuf_data_room_size(pool);

	*mbufp = rte_mbuf_raw_alloc(pool);
	if (*mbufp == NULL) {
		return false;
	}

	struct rte_mbuf* buf_symbol = (struct rte_mbuf*) malloc(pool->elt_size);
	if (buf_symbol == NULL) {
		rte_pktmbuf_free(*mbufp);
		return false;
	}

	// Make the packet symbolic
	klee_make_symbolic(buf_symbol, pool->elt_size, "buf_value");
	memcpy(mbufp, buf_symbol, pool->elt_size);
	free(buf_symbol);

	// Explicitly make the content symbolic - validator depends on an user_buf symbol for the proof
	struct stub_mbuf_content* buf_content_symbol = (struct stub_mbuf_content*) malloc(sizeof(struct stub_mbuf_content));
	if (buf_content_symbol == NULL) {
		rte_pktmbuf_free(*mbufp);
		return false;
	}
	klee_make_symbolic(buf_content_symbol, sizeof(struct stub_mbuf_content), "user_buf");
	memcpy((char*) *mbufp + mbuf_size, buf_content_symbol, sizeof(struct stub_mbuf_content));
	free(buf_content_symbol);

	// We do not support chained mbufs for now, make sure the NF doesn't touch them
	struct rte_mbuf* buf_next = (struct rte_mbuf*) malloc(pool->elt_size);
	if (buf_next == NULL) {
		rte_pktmbuf_free(*mbufp);
		return false;
	}
	klee_forbid_access(buf_next, pool->elt_size, "buf_next");

	// Keep concrete values for what a driver guarantees
	// (assignments are in the same order as the rte_mbuf declaration)
	(*mbufp)->buf_addr = (char*) (*mbufp) + mbuf_size;
	(*mbufp)->buf_iova = (rte_iova_t) (*mbufp)->buf_addr; // we assume VA = PA
	// TODO: make data_off symbolic (but then we get symbolic pointer addition...)
	// Alternative: Somehow prove that the code never touches anything outside of the [data_off, data_off+data_len] range...
	(*mbufp)->data_off = 0; // klee_range(0, pool->elt_size - sizeof(struct stub_mbuf_content), "data_off");
	(*mbufp)->refcnt = 1;
	(*mbufp)->nb_segs = 1; // TODO do we want to make a possibility of multiple packets? Or we could just prove the NF never touches this...
	(*mbufp)->port = device;
	(*mbufp)->ol_flags = 0;
	// packet_type is symbolic
	(*mbufp)->pkt_len = sizeof(struct stub_mbuf_content);
	(*mbufp)->data_len = sizeof(struct stub_mbuf_content); // TODO ideally those should be symbolic...
	// vlan_tci is symbolic
	// hash is symbolic
	// vlan_tci_outer is symbolic
	(*mbufp)->buf_len = (uint16_t) buf_len;
	// timestamp is symbolic
	(*mbufp)->userdata = NULL;
	(*mbufp)->pool = pool;
	(*mbufp)->next = buf_next;
	// tx_offload is symbolic
	(*mbufp)->priv_size = priv_size;
	// timesync is symbolic
	// seqn is symbolic

	rte_mbuf_sanity_check(*mbufp, 1 /* is head mbuf */);

	return true;
}

void
stub_core_mbuf_free(struct rte_mbuf* mbuf)
{
	// Undo our pseudo-chain trickery (see stub_core_mbuf_create)
	klee_allow_access(mbuf->next, mbuf->pool->elt_size);
	free(mbuf->next);
	mbuf->next = NULL;

	rte_pktmbuf_free(mbuf);
}
