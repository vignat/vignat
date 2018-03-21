// used with VeriFast, cannot use #pragma
#ifndef CORE_STUB_H
#define CORE_STUB_H

#include <stdbool.h>
#include <stdint.h>

#include <rte_mempool.h>

#include <lib/stubs/mbuf_content.h>

// HACK: see rte_mbuf.h for an explanation
#include "include_ignored_by_verifast.h"
#ifdef VIGOR_STUB_DPDK
#include <_internal_rte_mbuf.h>
#else
#ifdef _NO_VERIFAST_
struct rte_mbuf;
#else
#include <_internal_rte_mbuf.h>
#endif
#endif

// VeriFast definitions used in the tracing contracts
/*@
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
