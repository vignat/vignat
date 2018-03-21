// used with VeriFast, cannot use #pragma
#ifndef MBUF_CONTENT_H
#define MBUF_CONTENT_H

#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_tcp.h>

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
@*/

#endif
