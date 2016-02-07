
//A workaround for the VeriFast bug: failing on the unsigned short/char
// fields of an inductive datatype.
typedef unsigned int ui8;
typedef unsigned int ui16;
typedef unsigned int ui32;

/*@
  inductive int_key_i = int_key_c(ui16, ui16, ui32, ui32, ui8, ui8);
  inductive ext_key_i = ext_key_c(ui16, ui16, ui32, ui32, ui8, ui8);

  inductive flow_i = flow_c(int_key_i, ext_key_i, ui16, ui16, ui16,
                            ui32, ui32, ui32,
                            ui8, ui8, ui8,
                            ui32);

  fixpoint ui16 ik_isprt_a(int_key_i k) {
    switch(k){case int_key_c(ret, x2, x3, x4, x5, x6): return ret;}
  }
  fixpoint ui16 ik_dprt_a(int_key_i k) {
    switch(k){case int_key_c(x2, ret, x3, x4, x5, x6): return ret;}
  }
  fixpoint ui32 ik_isip_a(int_key_i k) {
    switch(k){case int_key_c(x2, x3, ret, x4, x5, x6): return ret;}
  }
  fixpoint ui32 ik_dip_a(int_key_i k) {
    switch(k){case int_key_c(x2, x3, x4, ret, x5, x6): return ret;}
  }
  fixpoint ui8 ik_idid_a(int_key_i k) {
    switch(k){case int_key_c(x2, x3, x4, x5, ret, x6): return ret;}
  }
  fixpoint ui8 ik_prtcl_a(int_key_i k) {
    switch(k){case int_key_c(x2, x3, x4, x5, x6, ret): return ret;}
  }

  fixpoint ui16 ek_esprt_a(ext_key_i k) {
    switch(k){case ext_key_c(ret, x2, x3, x4, x5, x6): return ret;}
  }
  fixpoint ui16 ek_dprt_a(ext_key_i k) {
    switch(k){case ext_key_c(x2, ret, x3, x4, x5, x6): return ret;}
  }
  fixpoint ui32 ek_esip_a(ext_key_i k) {
    switch(k){case ext_key_c(x2, x3, ret, x4, x5, x6): return ret;}
  }
  fixpoint ui32 ek_dip_a(ext_key_i k) {
    switch(k){case ext_key_c(x2, x3, x4, ret, x5, x6): return ret;}
  }
  fixpoint ui8 ek_edid_a(ext_key_i k) {
    switch(k){case ext_key_c(x2, x3, x4, x5, ret, x6): return ret;}
  }
  fixpoint ui8 ek_prtcl_a(ext_key_i k) {
    switch(k){case ext_key_c(x2, x3, x4, x5, x6, ret): return ret;}
  }

  fixpoint int_key_i fl_ik_a(flow_i f) {
    switch(f){case flow_c(ret, x1, x2, x3, x4,
                          x5, x6, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }
  fixpoint ext_key_i fl_ek_a(flow_i f) {
    switch(f){case flow_c(x1, ret, x2, x3, x4,
                          x5, x6, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }
  fixpoint ui16 fl_isprt_a(flow_i f) {
    switch(f){case flow_c(x1, x2, ret, x3, x4,
                          x5, x6, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }

  fixpoint ui16 fl_esprt_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, ret, x4,
                          x5, x6, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }

  fixpoint ui16 fl_dprt_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, ret,
                          x5, x6, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }

  fixpoint ui32 fl_isip_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          ret, x6, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }
  fixpoint ui32 fl_esip_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          x6, ret, x7,
                          x8, x9, x10,
                          x11): return ret;}
  }
  fixpoint ui32 fl_dip_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          x6, x7, ret,
                          x8, x9, x10,
                          x11): return ret;}
  }
  fixpoint ui8 fl_idid_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          x6, x7, x8,
                          ret, x9, x10,
                          x11): return ret;}
  }
  fixpoint ui8 fl_edid_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          x6, x7, x8,
                          x9, ret, x10,
                          x11): return ret;}
  }
  fixpoint ui8 fl_prtcl_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          x6, x7, x8,
                          x9, x10, ret,
                          x11): return ret;}
  }
  fixpoint ui32 fl_tstmp_a(flow_i f) {
    switch(f){case flow_c(x1, x2, x3, x4, x5,
                          x6, x7, x8,
                          x9, x10, x11,
                          ret): return ret;}
  }

  predicate int_key_p(struct int_key* p, int_key_i k) =
    p->int_src_port |-> ik_isprt_a(k) &*&
    p->dst_port |-> ik_dprt_a(k) &*&
    p->int_src_ip |-> ik_isip_a(k) &*&
    p->dst_ip |-> ik_dip_a(k) &*&
    p->int_device_id |-> ik_idid_a(k) &*&
    p->protocol |-> ik_prtcl_a(k);

  predicate ext_key_p(struct ext_key* p, ext_key_i k) =
    p->ext_src_port |-> ek_esprt_a(k) &*&
    p->dst_port |-> ek_dprt_a(k) &*&
    p->ext_src_ip |-> ek_esip_a(k) &*&
    p->dst_ip |-> ek_dip_a(k) &*&
    p->ext_device_id |-> ek_edid_a(k) &*&
    p->protocol |-> ek_prtcl_a(k);

  predicate flow_p(struct flow* p, flow_i f) =
    p->ik |-> ?ik &*& int_key_p(&ik, fl_ik_a(f));

  @*/
