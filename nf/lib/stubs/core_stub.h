// used with VeriFast, cannot use #pragma
#ifndef CORE_STUB_H
#define CORE_STUB_H

#include <stdbool.h>
#include <stdint.h>

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mempool.h>
#include <rte_tcp.h>

// HACK: see rte_mbuf.h for an explanation
#include <_internal_rte_mbuf.h>


// TODO more complete stub content?
// do change the total_len in rx if this is changed!
struct stub_mbuf_content {
	struct ether_hdr ether;
	struct ipv4_hdr ipv4;
	struct tcp_hdr tcp;
}
// We need to pack the structure so offsets are correct, but only if we're not within VeriFast, cause VeriFast doesn't know about it
#ifdef KLEE_VERIFICATION
 __attribute__((packed))
#endif
;

// VeriFast definitions used in the tracing contracts
/*@
    inductive ether_addri = eaddrc(int, int, int, int, int, int);
    predicate ether_addrp(struct ether_addr* ptr; ether_addri addr) =
      struct_ether_addr_padding(ptr) &*&
      ptr->a |-> ?a &*&
      ptr->b |-> ?b &*&
      ptr->c |-> ?c &*&
      ptr->d |-> ?d &*&
      ptr->e |-> ?e &*&
      ptr->f |-> ?f &*&
      addr == eaddrc(a, b, c, d, e, f);

    inductive ether_hdri = ether_hdrc(ether_addri, ether_addri, int);
    predicate ether_hdrp(struct ether_hdr *ether; ether_hdri hdr) =
      ether_addrp(&ether->d_addr, ?daddr) &*&
      ether_addrp(&ether->s_addr, ?saddr) &*&
      ether->ether_type |-> ?et &*&
      hdr == ether_hdrc(saddr, daddr, et);

    inductive ipv4_hdri = ipv4_hdrc(int, int, int, int, int, int, int, int, int);
    predicate ipv4_hdrp(struct ipv4_hdr* hdr; ipv4_hdri val) =
      hdr->version_ihl |-> ?vihl &*&
      hdr->type_of_service |-> ?tos &*&
      hdr->total_length |-> ?len &*&
      hdr->packet_id |-> ?pid &*&
      hdr->fragment_offset |-> ?foff &*&
      hdr->time_to_live |-> ?ttl &*&
      hdr->next_proto_id |-> ?npid &*&
      // no checksum
      hdr->src_addr |-> ?saddr &*&
      hdr->dst_addr |-> ?daddr &*&
      val == ipv4_hdrc(vihl, tos, len, pid, foff, ttl, npid, saddr, daddr) &*&
      len == 10240;
      //FIXME: ^^ generalize for all values

    inductive tcp_hdri = tcp_hdrc(int, int, int, int, int, int, int, int);
    predicate tcp_hdrp(struct tcp_hdr* hdr; tcp_hdri val) =
      hdr->src_port |-> ?srcp &*&
      hdr->dst_port |-> ?dstp &*&
      hdr->sent_seq |-> ?seq &*&
      hdr->recv_ack |-> ?ack &*&
      hdr->data_off |-> ?doff &*&
      hdr->tcp_flags |-> ?flags &*&
      hdr->rx_win |-> ?win &*&
      // no checksum
      hdr->tcp_urp |-> ?urp &*&
      val == tcp_hdrc(srcp, dstp, seq, ack, doff, flags, win, urp);

    inductive user_bufi = user_bufc(ether_hdri, ipv4_hdri, tcp_hdri);
    predicate user_bufferp(struct stub_mbuf_content *buf; user_bufi ub) =
      ether_hdrp(&buf->ether, ?hdr) &*&
      ipv4_hdrp(&buf->ipv4, ?ipv4) &*&
      tcp_hdrp(&buf->tcp, ?tcp) &*&
      ub == user_bufc(hdr, ipv4, tcp);

    inductive rte_mbufi = rte_mbufc(user_bufi, int, int, int);
    predicate mbufp(struct rte_mbuf *mbuf; rte_mbufi val) =
      mbuf->buf_addr |-> ?ba &*&
      mbuf->buf_iova |-> ?bfa &*&
      mbuf->data_off |-> ?doff &*&
      mbuf->refcnt |-> ?rcnt &*&
      mbuf->nb_segs |-> ?nbsegs &*&
      mbuf->port |-> ?port &*&
      mbuf->ol_flags |-> ?olflags &*&
      mbuf->packet_type |-> ?ptype &*&
      mbuf->pkt_len |-> ?pktlen &*&
      mbuf->data_len |-> ?dlen &*&
      mbuf->vlan_tci |-> ?vlantci &*&
      mbuf->hash |-> ?hash &*&
      mbuf->vlan_tci_outer |-> ?vtcio &*&
      mbuf->buf_len |-> ?bl &*&
      mbuf->timestamp |-> ?tmstp &*&
      mbuf->udata64 |-> ?udata64 &*&
      mbuf->pool |-> ?pool &*&
      mbuf->next |-> ?next &*&
      mbuf->tx_offload |-> ?txoff &*&
      mbuf->priv_size |-> ?psize &*&
      mbuf->timesync |-> ?ts &*&
      mbuf->seqn |-> ?seqn &*&
      user_bufferp(ba, ?ub) &*&
      val == rte_mbufc(ub, port, ptype, doff) &*&
      doff == 0;
      //TODO: ^^^ is it really always so?
@*/


// TODO add tracing for packet details

// mbuf tracing
// HACK:
// - First, we use a double-pointer for trace_rx because the Validator doesn't support single-pointer out params
// - Second, we make _tx return a int (instead of letting callers just not call it) because the Validator
//   is currently written with the assumption that "sending" means "trying to send"; we'd need to fix that...
// - Third, we use an int instead of a bool because the Validator doesn't support bools

void stub_core_trace_rx(struct rte_mbuf** mbuf);
//@ requires *mbuf |-> _;
//@ ensures *mbuf |-> ?mb &*& mbufp(mb, _);

uint8_t stub_core_trace_tx(struct rte_mbuf* mbuf, uint16_t device);
//@ requires mbufp(mbuf, ?mb);
//@ ensures result <= 1 &*& (result == 0 ? mbufp(mbuf, mb) : true);

void stub_core_trace_free(struct rte_mbuf* mbuf);
//@ requires mbufp(mbuf,_);
//@ ensures true;


// mbuf create/free
bool stub_core_mbuf_create(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufp);
void stub_core_mbuf_free(struct rte_mbuf* mbuf);

#endif
