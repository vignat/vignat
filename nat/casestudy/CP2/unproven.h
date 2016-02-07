#include "lib/flow.h"

//@ #include "lib/predicates.gh"
#define RTE_MAX_ETH_PORTS 2
/*@ predicate flw_consist(struct int_key* a, struct ext_key* b, struct flow* v) =
      a->int_src_port |-> ?ik_isprt &*&
      a->dst_port |-> ?ik_dprt &*&
      a->int_src_ip |-> ?ik_isip &*&
      a->dst_ip |-> ?ik_dip &*&
      a->int_device_id |-> ?ik_idid &*&
      a->protocol |-> ?ik_prtcl &*&
      b->ext_src_port |-> ?ek_esprt &*&
      b->dst_port |-> ?ek_dprt &*&
      b->ext_src_ip |-> ?ek_esip &*&
      b->dst_ip |-> ?ek_dip &*&
      b->ext_device_id |-> ?ek_edid &*&
      b->protocol |-> ?ek_prtcl &*&
      //FIXME:Check for v->ik and v->ek
      v->int_src_port |-> ?fl_isprt &*&
      v->ext_src_port |-> ?fl_esprt &*&
      v->dst_port |-> ?fl_dprt &*&
      v->int_src_ip |-> ?fl_isip &*&
      v->ext_src_ip |-> ?fl_esip &*&
      v->dst_ip |-> ?fl_dip &*&
      v->int_device_id |-> ?fl_idid &*&
      v->ext_device_id |-> ?fl_edid &*&
      v->protocol |-> ?fl_prtcl &*&
      v->timestamp |-> ?fl_tstmp &*&
      ik_isprt == fl_isprt &&
      ik_dprt == fl_dprt &&
      ik_isip == fl_isip &&
      ik_dip == fl_dip &&
      ik_idid == fl_idid &&
      ik_prtcl == fl_prtcl &&
      ek_esprt == fl_esprt &&
      ek_dprt == fl_dprt &&
      ek_esip == fl_esip &&
      ek_dip == fl_dip &&
      ek_edid == fl_edid &&
      ek_prtcl == fl_prtcl &&
      ( 0 <= fl_idid && fl_idid < RTE_MAX_ETH_PORTS) &&
      ( 0 <= fl_edid && fl_edid < RTE_MAX_ETH_PORTS);
      //TODO: handle the flow->timestamp < get_start_time()
  @*/

/*@ lemma void flow_is_consistent(struct ext_key* b, struct flow* v);
    requires double_map_p(?map, ?sza, ?szb, ?szv) &*&
             domap_flow_at(map, domap_get_b(map, b), v);
    ensures flw_consist(?a, b, v) &*& double_map_p(map, sza, szb, szv);
    @*/
