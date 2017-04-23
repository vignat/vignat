
open Core.Std
open Fspec_api
open Ir

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""
let last_device_id = ref ""

let last_time_for_index_alloc = ref ""
let the_array_lcc_is_local = ref true


let gen_get_fp map_name =
  match !last_index_key with
  | Int-> "dmap_get_k1_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"
  | Ext -> "dmap_get_k2_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"

let capture_map map_name ptr_num {args;tmp_gen;_} =
  "//@ assert dmappingp<int_k,ext_k,flw>(?" ^ (tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args ptr_num) ^ ");\n"

let capture_map_after map_name ptr_num (params:lemma_params) =
  "//@ assert dmappingp<int_k,ext_k,flw>(?" ^ (params.tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn params.args ptr_num) ^ ");\n"

let capture_chain_after ch_name ptr_num (params:lemma_params) =
  "//@ assert double_chainp(?" ^ (params.tmp_gen ch_name) ^ ", " ^
  (List.nth_exn params.args ptr_num) ^ ");\n"

let capture_map_ex map_name vk1 vk2 ptr_num {args;tmp_gen} =
  "//@ assert dmappingp<int_k,ext_k,flw>(?" ^ (tmp_gen map_name) ^
  ",_,_,_,_,_,_,_,_,?" ^ (tmp_gen vk1) ^ ",?" ^ (tmp_gen vk2) ^
  ",_,_," ^
  (List.nth_exn args ptr_num) ^ ");\n"

let capture_chain ch_name ptr_num {args;tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen ch_name) ^ ", " ^
  (List.nth_exn args ptr_num) ^ ");\n"

let dmap_struct = Ir.Str ( "DoubleMap", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )
let ext_key_struct = Ir.Str ( "ext_key", ["ext_src_port", Uint16;
                                          "dst_port", Uint16;
                                          "ext_src_ip", Uint32;
                                          "dst_ip", Uint32;
                                          "ext_device_id", Uint8;
                                          "protocol", Uint8;] )
let int_key_struct = Ir.Str ( "int_key", ["int_src_port", Uint16;
                                          "dst_port", Uint16;
                                          "int_src_ip", Uint32;
                                          "dst_ip", Uint32;
                                          "int_device_id", Uint8;
                                          "protocol", Uint8;] )
let flw_struct = Ir.Str ("flow", ["ik", int_key_struct;
                                  "ek", ext_key_struct;
                                  "int_src_port", Uint16;
                                  "ext_src_port", Uint16;
                                  "dst_port", Uint16;
                                  "int_src_ip", Uint32;
                                  "ext_src_ip", Uint32;
                                  "dst_ip", Uint32;
                                  "int_device_id", Uint8;
                                  "ext_device_id", Uint8;
                                  "protocol", Uint8;])
let arr_bat_struct = Ir.Str ( "ArrayBat", [] )
let arr_lcc_struct = Ir.Str ( "ArrayLcc", [] )
let arr_rq_struct = Ir.Str ( "ArrayRq", [] )
let arr_u16_struct = Ir.Str ( "ArrayU16", [] )
let batcher_struct = Ir.Str ( "Batcher", [] )
let lcore_conf_struct = Ir.Str ( "lcore_conf", ["n_rx_queue", Uint16;
                                                "rx_queue_list", arr_rq_struct;
                                                "tx_queue_id", arr_u16_struct;
                                                "tx_mbufs", arr_bat_struct;])
let lcore_rx_queue_struct = Ir.Str ( "lcore_rx_queue", ["port_id", Uint8;
                                                        "queue_id", Uint8;])

let ether_hdr_struct = Ir.Str ("ether_hdr", ["ether_type", Uint16;])
let ipv4_hdr_struct = Ir.Str ("ipv4_hdr", ["version_ihl", Uint8;
                                           "type_of_service", Uint8;
                                           "total_length", Uint16;
                                           "packet_id", Uint16;
                                           "fragment_offset", Uint16;
                                           "time_to_live", Uint8;
                                           "next_proto_id", Uint8;
                                           (* Too difficult to check
                                              "hdr_checksum", Uint16; *)
                                           "src_addr", Uint32;
                                           "dst_addr", Uint32;])
let tcp_hdr_struct = Ir.Str ("tcp_hdr", ["src_port", Uint16;
                                         "dst_port", Uint16;
                                         "sent_seq", Uint32;
                                         "recv_ack", Uint32;
                                         "data_off", Uint8;
                                         "tcp_flags", Uint8;
                                         "rx_win", Uint16;
                                         (* too difficult to check
                                            "cksum", Uint16; *)
                                         "tcp_urp", Uint16;])

let user_buf_struct = Ir.Str ("user_buf", ["ether", ether_hdr_struct;
                                           "ipv4", ipv4_hdr_struct;
                                           "tcp", tcp_hdr_struct;])
let rte_mbuf_struct = Ir.Str ( "rte_mbuf",
                               ["buf_addr", Ptr user_buf_struct;
                                "buf_physaddr", Uint64;
                                "buf_len", Uint16;
                                "data_off", Uint16;
                                "refcnt", Uint16;
                                "nb_segs", Uint8;
                                "port", Uint8;
                                "ol_flags", Uint64;
                                "packet_type", Uint32;
                                "pkt_len", Uint32;
                                "data_len", Uint16;
                                "vlan_tci", Uint16;
                                "hash", Uint32;
                                "seqn", Uint32;
                                "vlan_tci_outer", Uint16;
                                "udata64", Uint64;
                                "pool", Ptr Void;
                                "next", Ptr Void;
                                "tx_offload", Uint64;
                                "priv_size", Uint16;
                                "timesync", Uint16] )

let copy_user_buf var_name ptr =
  deep_copy
    {Ir.name=var_name;
     Ir.value={v=Deref {v=Ir.Id ("((" ^ ptr ^ ")->buf_addr)");
                        t=Ptr user_buf_struct};
               t=user_buf_struct}}

let fun_types =
  String.Map.of_alist_exn
    ["current_time", {ret_type = Uint32;
                      arg_types = [];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [
                        (fun params ->
                        "uint32_t now = " ^ (params.ret_name) ^ ";\n")];};
     "start_time", {ret_type = Uint32;
                    arg_types = [];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
     "dmap_allocate", {ret_type = Sint32;
                       arg_types = stt
                         [Ptr (Ctm "map_keys_equality"); Ptr (Ctm "map_key_hash");
                          Ptr (Ctm "map_keys_equality"); Ptr (Ctm "map_key_hash");
                          Sint32; Ptr (Ctm "uq_value_copy");
                          Ptr (Ctm "uq_value_destr");
                          Ptr (Ctm "dmap_extract_keys"); Ptr (Ctm "dmap_pack_keys");
                          Sint32; Sint32;
                          Ptr (Ptr dmap_struct)];
                       extra_ptr_types = [];
                       lemmas_before = [
                         tx_bl "produce_function_pointer_chunk \
                                map_keys_equality<int_k>(int_key_eq)(int_k_p)(a, b) \
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_key_hash<int_k>(int_key_hash)\
                                (int_k_p, int_hash)(a)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_keys_equality<ext_k>(ext_key_eq)(ext_k_p)(a, b)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_key_hash<ext_k>(ext_key_hash)\
                                (ext_k_p, ext_hash)(a)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                dmap_extract_keys<int_k,ext_k,flw>\
                                (flow_extract_keys)\
                                (int_k_p, ext_k_p, flw_p, flow_p,\
                                 flow_keys_offsets_fp,\
                                 flw_get_ik,\
                                 flw_get_ek)(a, b, c)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                dmap_pack_keys<int_k,ext_k,flw>\
                                (flow_pack_keys)\
                                (int_k_p, ext_k_p, flw_p, flow_p,\
                                 flow_keys_offsets_fp,\
                                 flw_get_ik,\
                                 flw_get_ek)(a, b, c)\
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                uq_value_destr<flw>\
                                (flow_destroy)\
                                (flw_p, sizeof(struct flow))(a)\
                                {\
                                call();\
                                }";
                         (fun {args;_} ->
                            "/*@\
                             assume(sizeof(struct flow) == " ^
                            (List.nth_exn args 4) ^ ");\n@*/ " ^
                             "/*@ produce_function_pointer_chunk \
                             uq_value_copy<flw>(flow_cpy)\
                             (flw_p, " ^ (List.nth_exn args 4) ^ ")(a,b)\
                             {\
                             call();\
                             }@*/");
                         tx_bl "close dmap_key_val_types\
                                (ikc(0,0,0,0,0,0), ekc(0,0,0,0,0,0),\
                                      flwc(ikc(0,0,0,0,0,0),\
                                           ekc(0,0,0,0,0,0),\
                                           0,0,0,0,0,0,0,0,0));";
                         tx_bl "close dmap_record_property1(nat_int_fp);";
                         (fun _ -> "int start_port;\n");
                         tx_bl "close dmap_record_property2\
                                ((nat_ext_fp)(start_port));"];
                       lemmas_after = [
                         tx_l "empty_dmap_cap\
                               <int_k,ext_k,flw>(65536);";];};
     "dmap_set_entry_condition", {ret_type = Void;
                                  arg_types = stt [Ptr (Ctm "entry_condition")];
                                  extra_ptr_types = [];
                                  lemmas_before = [];
                                  lemmas_after = [];};
     "dchain_allocate", {ret_type = Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                               "empty_dmap_dchain_coherent\
                                <int_k,ext_k,flw>(65536);";
                           tx_l "index_range_of_empty(65536, 0);";];};
     "loop_invariant_consume", {ret_type = Void;
                                arg_types = stt [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Uint32;
                                             Uint32;
                                             Sint32;
                                             Sint32];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun {args;_} ->
                                     "//@ assume(start_port == " ^
                                     List.nth_exn args 5 ^");");
                                  (fun {args;_} ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ ", " ^
                                     List.nth_exn args 2 ^ ", " ^
                                     List.nth_exn args 3 ^ ", " ^
                                     List.nth_exn args 4 ^ ", " ^
                                     List.nth_exn args 5 ^ "); @*/");
                                ];
                                lemmas_after = [];};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = stt [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Ptr Uint32;
                                             Ptr Uint32;
                                             Sint32;
                                             Sint32];
                                extra_ptr_types = [];
                                lemmas_before = [
                                  (fun _ ->
                                     "int start_port;\n");];
                                lemmas_after = [
                                  (fun params ->
                                     the_array_lcc_is_local := false;
                                     "");
                                  (fun params ->
                                     "/*@ open evproc_loop_invariant(?mp, \
                                      ?chp, *" ^
                                     List.nth_exn params.args 2 ^ ", *" ^
                                     List.nth_exn params.args 3 ^ ", " ^
                                     List.nth_exn params.args 4 ^ ", " ^
                                     List.nth_exn params.args 5 ^ ");@*/");
                                  (fun params ->
                                     "//@ assume(" ^
                                     List.nth_exn params.args 5 ^ " == start_port);");
                                  tx_l "assert dmap_dchain_coherent(?map,?chain);";
                                  tx_l "coherent_same_cap(map, chain);";
                                  tx_l "dmap<int_k,ext_k,flw> initial_double_map = map;";
                                  tx_l "dchain initial_double_chain = chain;"
                                ];};
     "dmap_get_b", {ret_type = Sint32;
                    arg_types = stt [Ptr dmap_struct; Ptr ext_key_struct; Ptr Sint32;];
                    extra_ptr_types = [];
                    lemmas_before = [
                      capture_map "cur_map" 0;
                      (fun {args;_} ->
                         last_device_id :=
                           "(" ^ List.nth_exn args 1 ^ ")->ext_device_id";
                         "/*@ close ext_k_p(" ^ List.nth_exn args 1 ^
                         ", ekc(user_buf0_36, user_buf0_34, " ^
                         "user_buf0_30, user_buf0_26, (" ^ List.nth_exn args 1 ^
                         ")->ext_device_id,\
                          user_buf0_23)); @*/"); ];
                    lemmas_after = [
                      tx_l "open (ext_k_p(_,_));";
                      (fun params ->
                         "/*@ {\n assert dmap_dchain_coherent(" ^
                         (params.tmp_gen "cur_map") ^
                         ", ?cur_ch);\n\
                          contains_ext_k_abstract(" ^
                         (params.tmp_gen "cur_map") ^
                         ", cur_ch,\n ekc(user_buf0_36, user_buf0_34, " ^
                         "user_buf0_30, user_buf0_26, (" ^
                         List.nth_exn params.args 1 ^
                         ")->ext_device_id,\
                          user_buf0_23));\n}@*/");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k2_limits(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, (" ^
                           List.nth_exn params.args 1 ^
                           ")->ext_device_id, user_buf0_23));\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k2_get_val(" ^
                           (params.tmp_gen "cur_map") ^
                           ",ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, (" ^
                           List.nth_exn params.args 1 ^
                           ")->ext_device_id, user_buf0_23));\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n assert dmap_dchain_coherent(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ?cur_ch);\n" ^
                           "ext_k ek = ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, (" ^
                           List.nth_exn params.args 1 ^
                           ")->ext_device_id, user_buf0_23);\n"^
                           "get_flow_by_ext_abstract(" ^
                           (params.tmp_gen "cur_map") ^ ", cur_ch, ek);\n" ^
                           "coherent_dmap_used_dchain_allocated(" ^
                           (params.tmp_gen "cur_map") ^ ", cur_ch, dmap_get_k2_fp(" ^
                           (params.tmp_gen "cur_map") ^ ", ek));\n}");
                      (fun params ->
                         last_index_gotten :=
                           "ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, (" ^
                           List.nth_exn params.args 1 ^
                           ")->ext_device_id, user_buf0_23)";
                         last_index_key := Ext;
                         last_indexing_succ_ret_var := params.ret_name;
                         "");
                    ];};
     "dmap_get_a", {ret_type = Sint32;
                    arg_types = stt [Ptr dmap_struct; Ptr int_key_struct; Ptr Sint32;];
                    extra_ptr_types = [];
                    lemmas_before = [
                      capture_map "cur_map" 0;
                      (fun {args;_} ->
                         last_device_id :=
                           "(" ^ List.nth_exn args 1 ^ ")->int_device_id";
                         "/*@ close int_k_p(" ^ List.nth_exn args 1 ^
                         ", ikc(user_buf0_34, user_buf0_36,\
                          user_buf0_26, user_buf0_30, (" ^ List.nth_exn args 1 ^
                         ")->int_device_id, user_buf0_23)); @*/"
                      );];
                    lemmas_after = [
                      tx_l "open (int_k_p(_,_));";
                      (fun params ->
                         "/*@ {\n assert dmap_dchain_coherent(" ^
                         (params.tmp_gen "cur_map") ^
                         ", ?cur_ch);\n\
                          contains_int_k_abstract(" ^
                         (params.tmp_gen "cur_map") ^
                         ", cur_ch,\n ikc(user_buf0_34, user_buf0_36, \
                          user_buf0_26, user_buf0_30, (" ^ List.nth_exn params.args 1 ^
                         ")->int_device_id, user_buf0_23));\n}@*/");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k1_limits(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, (" ^ List.nth_exn params.args 1 ^
                           ")->int_device_id, user_buf0_23));\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n dmap_get_k1_get_val(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, (" ^ List.nth_exn params.args 1 ^
                           ")->int_device_id, user_buf0_23));\n}");
                      on_rez_nz
                        (fun params ->
                           "{\n" ^
                           "int_k ik = ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, (" ^
                           List.nth_exn params.args 1 ^
                           ")->int_device_id, user_buf0_23);\n" ^
                           " assert dmap_dchain_coherent(" ^
                           (params.tmp_gen "cur_map") ^ ", ?cur_ch);\n" ^
                           "get_flow_by_int_abstract(" ^
                           (params.tmp_gen "cur_map") ^ ", cur_ch, ik);\n" ^
                           "coherent_dmap_used_dchain_allocated(" ^
                           (params.tmp_gen "cur_map") ^
                           ", cur_ch, dmap_get_k1_fp(" ^
                           (params.tmp_gen "cur_map") ^
                           ", ik));\n}");
                      (fun params ->
                         last_index_gotten :=
                           "ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, (" ^ List.nth_exn params.args 1 ^
                           ")->int_device_id, user_buf0_23)";
                         last_index_key := Int;
                         last_indexing_succ_ret_var := params.ret_name;
                         "");
                    ];};
     "dmap_put", {ret_type = Sint32;
                  arg_types = stt [Ptr dmap_struct; Ptr flw_struct; Sint32;];
                  extra_ptr_types = [];
                  lemmas_before = [
                    capture_map_ex "cur_map" "vk1" "vk2" 0;
                    (fun {args;_} -> "/*@ close int_k_p(" ^ (List.nth_exn args 1) ^
                    ".ik, ikc(user_buf0_34, user_buf0_36, user_buf0_26,\
                     user_buf0_30, " ^
                           !last_device_id ^
                           ", user_buf0_23));@*/");
                    (fun {args;_} -> "/*@ close ext_k_p(" ^ (List.nth_exn args 1) ^
                    ".ek, ekc(new_index_2_0, user_buf0_36, external_ip, user_buf0_30,\
                     1, user_buf0_23));@*/");
                    (fun {args;_} -> "/*@ close flw_p(" ^ (List.nth_exn args 1) ^
                    ", flwc(ikc(user_buf0_34, user_buf0_36, user_buf0_26, user_buf0_30,\
                     " ^
                           !last_device_id ^
                           ", user_buf0_23), ekc(new_index_2_0, user_buf0_36, external_ip, user_buf0_30,\
                     1, user_buf0_23), user_buf0_34, new_index_2_0, user_buf0_36, user_buf0_26,\
                     external_ip, user_buf0_30, " ^
                           !last_device_id ^
                           ", 1, user_buf0_23));@*/");
                    (fun {args;tmp_gen;_} ->
                       "/*@{\n\
                        assert dmap_dchain_coherent(" ^
                         (tmp_gen "cur_map") ^
                       ", ?cur_ch);\n\
                        ext_k ek = ekc(new_index_2_0, user_buf0_36,\
                        external_ip, user_buf0_30, 1, user_buf0_23);\n\
                        if (dmap_has_k2_fp(" ^ (tmp_gen "cur_map") ^
                       ", ek)) {\n\
                        int index = dmap_get_k2_fp(" ^ (tmp_gen "cur_map") ^
                       ", ek);\n\
                        dmap_get_k2_limits(" ^ (tmp_gen "cur_map") ^
                       ", ek);\n\
                        flw value = dmap_get_val_fp(" ^ (tmp_gen "cur_map") ^
                       ", index);\n\
                        dmap_get_by_index_rp(" ^ (tmp_gen "cur_map") ^
                       ", index);\n\
                        dmap_get_by_k2_invertible(" ^ (tmp_gen "cur_map") ^
                       ", ek);\n\
                        assert(index == " ^ (List.nth_exn args 2) ^ ");\n\
                        assert(true == dmap_index_used_fp(" ^ (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ "));\n\
                        coherent_dmap_used_dchain_allocated(" ^ (tmp_gen "cur_map") ^
                       ", cur_ch, " ^ (List.nth_exn args 2) ^ ");\n\
                        assert(true == dchain_allocated_index_fp(" ^
                       (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ "));\n\
                        assert(false);\n\
                        }\n\
                        }@*/");
                    (fun {args;tmp_gen;_} ->
                       "/*@{\n\
                        assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                       ", ?cur_ch);\n\
                        if (dmap_index_used_fp(" ^ (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ ")) {\n\
                        coherent_dmap_used_dchain_allocated(" ^ (tmp_gen "cur_map") ^
                       ", cur_ch, " ^ (List.nth_exn args 2) ^ ");\n\
                        }\n\
                        }@*/");
                    (fun {args;tmp_gen;_} ->
                       "/*@ dmap_put_preserves_cap(" ^ (tmp_gen "cur_map") ^
                       ", " ^ (List.nth_exn args 2) ^ ", flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, " ^
                           !last_device_id ^
                           ", user_buf0_23),\n\
                        ekc(new_index_2_0, user_buf0_36, external_ip, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, new_index_2_0, user_buf0_36, user_buf0_26,\n\
                        external_ip, user_buf0_30, " ^
                           !last_device_id ^
                           ", 1, user_buf0_23)," ^
                       (tmp_gen "vk1") ^ ", " ^ (tmp_gen "vk2") ^ "); @*/");
                    (fun _ ->
                       "/*@ flw the_inserted_flow = " ^
                       " flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, " ^
                       !last_device_id ^
                       ", user_buf0_23),\n\
                        ekc(new_index_2_0, user_buf0_36, external_ip, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, new_index_2_0, user_buf0_36, user_buf0_26,\n\
                        external_ip, user_buf0_30, " ^
                       !last_device_id ^
                       ", 1, user_buf0_23);@*/");
                    (fun {args;tmp_gen;_} ->
                      "/*@ {\n\
                       assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                      ", ?ch);\n\
                       int_k ik = ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, " ^
                       !last_device_id ^
                       ", user_buf0_23);\n\
                       ext_k ek = ekc(new_index_2_0, user_buf0_36,\
                       external_ip, user_buf0_30,\
                       1, user_buf0_23);\n\
                       coherent_dchain_non_out_of_space_map_nonfull(" ^
                      (tmp_gen "cur_map") ^ ", ch);\n" ^
                      "contains_ext_k_abstract(" ^
                      (tmp_gen "cur_map") ^
                      ", ch, ek);\n" ^
                      "flw the_flow_to_insert = flwc(ik, ek,\n\
                       user_buf0_34, new_index_2_0, user_buf0_36, user_buf0_26,\n\
                       external_ip, user_buf0_30, " ^
                       !last_device_id ^
                      ", 1, user_buf0_23);\n" ^
                       "add_flow_abstract(" ^ (tmp_gen "cur_map") ^
                       ", ch, the_flow_to_insert, " ^
                       (List.nth_exn args 2) ^ ", " ^
                       !last_time_for_index_alloc ^ ");\n} @*/");];
                  lemmas_after = [
                    tx_l "open flw_p(_,_);";
                    tx_l "open int_k_p(_,_);";
                    tx_l "open ext_k_p(_,_);";
                    (fun params ->
                       "/*@if (" ^ params.ret_name ^
                       "!= 0) {\n\
                        dmap_put_get(" ^
                       (params.tmp_gen "cur_map") ^
                       "," ^ (List.nth_exn params.args 2) ^ ",\
                        flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, " ^
                       !last_device_id ^
                           ", user_buf0_23),\n\
                        ekc(new_index_2_0, user_buf0_36, external_ip, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, new_index_2_0, user_buf0_36, user_buf0_26,\n\
                        external_ip, user_buf0_30, " ^
                           !last_device_id ^
                           ", 1, user_buf0_23),\n" ^
                       (params.tmp_gen "vk1") ^ ", " ^
                       (params.tmp_gen "vk2") ^ ");\n}@*/");
                    (fun params ->
                       "/*@if (" ^ params.ret_name ^
                       "!= 0) {\n\
                        assert dmap_dchain_coherent(" ^
                       (params.tmp_gen "cur_map") ^
                       ", ?cur_ch);\n\
                       int_k ik = ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, " ^
                       !last_device_id ^
                       ", user_buf0_23);\n\
                        ext_k ek = ekc(new_index_2_0, user_buf0_36,\
                        external_ip, user_buf0_30,\
                        1, user_buf0_23);\n\
                        flw the_flow_to_insert = flwc(ik, ek,\n\
                        user_buf0_34, new_index_2_0, user_buf0_36, user_buf0_26,\n\
                        external_ip, user_buf0_30, " ^
                       !last_device_id ^
                       ", 1, user_buf0_23);\n" ^
                      "coherent_put_allocated_preserves_coherent\n(" ^
                      (params.tmp_gen "cur_map") ^
                      ", cur_ch, ik , ek,\
                       the_flow_to_insert,\
                      " ^ (List.nth_exn params.args 2) ^ ", " ^
                      !last_time_for_index_alloc ^
                      ", " ^ (params.tmp_gen "vk1") ^ ", " ^
                      (params.tmp_gen "vk2") ^ ");\n}@*/");
                  ];};
     "dmap_get_value", {ret_type = Void;
                        arg_types = stt [Ptr dmap_struct; Sint32; Ptr flw_struct;];
                        extra_ptr_types = [];
                        lemmas_before = [
                          capture_map "cur_map" 0;
                          (fun {tmp_gen;_} ->
                             "/*@ {\
                              assert dmap_dchain_coherent(" ^ (tmp_gen "cur_map") ^
                             ", ?cur_ch);\n\
                              coherent_same_cap(" ^ (tmp_gen "cur_map") ^
                             ", cur_ch);\n\
                              }@*/");
                          (fun {args;_} ->
                             "//@ open_struct(" ^
                             (List.nth_exn args 2) ^ ");")];
                        lemmas_after = [
                          (fun params ->
                             "/*@{ if (" ^ !last_indexing_succ_ret_var ^
                             "!= 0) { \n\
                              assert dmap_dchain_coherent(" ^
                             (params.tmp_gen "cur_map") ^
                             ", ?cur_ch);\n\
                              coherent_dmap_used_dchain_allocated(" ^
                             (params.tmp_gen "cur_map") ^ ", cur_ch," ^
                             (gen_get_fp (params.tmp_gen "cur_map")) ^
                             ");\n\
                              }}@*/");
                          (fun _ -> "assert(0 <= " ^
                                    !last_device_id ^
                                    " && " ^
                                    !last_device_id ^
                                    " < RTE_MAX_ETHPORTS);");
                          (fun params ->
                             "/*@\
                              open flw_p(" ^ (List.nth_exn params.args 2) ^
                             ", _);\n\
                              @*/");
                          tx_l "open int_k_p(_,_);";
                          tx_l "open ext_k_p(_,_);";
                        ];};
     "expire_items", {ret_type = Sint32;
                      arg_types = stt [Ptr dchain_struct;
                                   Ptr dmap_struct;
                                   Uint32;];
                      extra_ptr_types = [];
                      lemmas_before = [
                        capture_chain "cur_ch" 0;
                        capture_map_ex "cur_map" "vk1" "vk2" 1;
                        (fun {args;tmp_gen;_} ->
                           if String.equal !last_index_gotten "" then ""
                           else
                           "/*@ { \n\
                            dmap_erase_all_has_trans(" ^
                           (tmp_gen "cur_map") ^
                           ", ikc(user_buf0_34,\
                            user_buf0_36, user_buf0_26, user_buf0_30, " ^
                           !last_device_id ^
                           ", user_buf0_23),\n\
                            dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           "), " ^ (tmp_gen "vk1") ^ ", " ^ (tmp_gen "vk2") ^
                           ");\n\
                            coherent_same_cap(" ^
                           (tmp_gen "cur_map") ^ ", " ^ (tmp_gen "cur_ch") ^
                           ");\n } @*/");
                        (fun {args;tmp_gen;_} ->
                           "//@ expire_flows_abstract(" ^ (tmp_gen "cur_map") ^
                           ", " ^ (tmp_gen "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^ ");");
                        (fun {args;tmp_gen;_} ->
                           "/*@ {\n\
                            expire_preserves_index_range(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ");\n
                           length_nonnegative(\
                            dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           "));\n\
                            if (length(dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ")) > 0 ) {\n\
                            expire_old_dchain_nonfull\
                            (" ^ (List.nth_exn args 0) ^ ", " ^
                           (tmp_gen "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ");\n\
                            }} @*/");
                        (fun {args;tmp_gen;_} ->
                           "/*@ dmap_erase_all_preserves_cap(" ^
                           (tmp_gen "cur_map") ^ ", " ^
                           "dchain_get_expired_indexes_fp(" ^
                           (tmp_gen "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^
                           "), " ^ (tmp_gen "vk1") ^ ", " ^
                           (tmp_gen "vk2") ^ "); @*/");
                        (fun {tmp_gen} ->
                           "/*@ coherent_same_cap(" ^
                           (tmp_gen "cur_map") ^ ", " ^ (tmp_gen "cur_ch") ^ ");@*/\n");
                        (fun {args;tmp_gen} ->
                           "//@ expire_olds_keeps_high_bounded(" ^
                           (tmp_gen "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^
                           ");\n");
                        ];
                      lemmas_after = [
                        capture_chain_after "ch_after_exp" 0;
                        capture_map_after "map_after_exp" 1;
                        (fun params ->
                           "//@out_of_space_abstract(" ^
                           (params.tmp_gen "map_after_exp") ^
                           ", " ^ (params.tmp_gen "ch_after_exp") ^ ");");
                        (fun params ->
                           "//@ dmap<int_k,ext_k,flw> map_after_expiration = " ^
                           (params.tmp_gen "map_after_exp") ^";\n" ^
                           "dchain chain_after_expiration = " ^
                           (params.tmp_gen "ch_after_exp") ^ ";";);
                      ];};
     "dchain_allocate_new_index", {ret_type = Sint32;
                                   arg_types = stt [Ptr dchain_struct; Ptr Sint32; Uint32;];
                                   extra_ptr_types = [];
                                   lemmas_before = [
                                     capture_chain "cur_ch" 0;
                                   ];
                                   lemmas_after = [
                                     on_rez_nz
                                       (fun params ->
                                          "{\n allocate_preserves_index_range(" ^
                                          (params.tmp_gen "cur_ch") ^
                                          ", *" ^
                                          (List.nth_exn params.args 1) ^ ", " ^
                                          (List.nth_exn params.args 2) ^ ");\n}");
                                     (fun params ->
                                        "//@ allocate_keeps_high_bounded(" ^
                                        (params.tmp_gen "cur_ch") ^
                                        ", *" ^ (List.nth_exn params.args 1) ^
                                        ", " ^ (List.nth_exn params.args 2) ^
                                        ");\n");
                                     (fun params ->
                                        last_time_for_index_alloc :=
                                          (List.nth_exn params.args 2);
                                        "");
                                     (fun params ->
                                        "int the_index_allocated = *" ^
                                        (List.nth_exn params.args 1) ^ ";\n");
                                   ];};
     "dchain_rejuvenate_index", {ret_type = Sint32;
                                 arg_types = stt [Ptr dchain_struct; Sint32; Uint32;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {args;tmp_gen} ->
                                      "/*@ {\n\
                                       assert dmap_dchain_coherent(?cur_map, " ^
                                      (tmp_gen "cur_ch") ^
                                      ");\n coherent_same_cap(cur_map, " ^
                                      (tmp_gen "cur_ch") ^ ");\n" ^
                                      "rejuvenate_flow_abstract(cur_map," ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      "dmap_get_val_fp(cur_map, " ^
                                      (List.nth_exn args 1) ^ ")," ^
                                      (List.nth_exn args 1) ^ ", " ^
                                      (List.nth_exn args 2) ^ ");\n" ^
                                      "} @*/");
                                   (fun {args;tmp_gen} ->
                                      "//@ rejuvenate_keeps_high_bounded(" ^
                                      (tmp_gen "cur_ch") ^
                                      ", " ^ (List.nth_exn args 1) ^
                                      ", " ^ (List.nth_exn args 2) ^
                                      ");\n");];
                                 lemmas_after = [
                                   (fun params ->
                                      "/*@ if (" ^ params.ret_name ^
                                      " != 0) { \n" ^
                                      "assert dmap_dchain_coherent(?cur_map,?ch);\n" ^
                                      "rejuvenate_preserves_coherent(cur_map, ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^ ");\n}@*/");
                                   (fun params ->
                                      "int the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};
     "array_bat_init", {ret_type = Void;
                        arg_types = stt [Ptr arr_bat_struct;];
                        extra_ptr_types = [];
                        lemmas_before = [];
                        lemmas_after = [];};
     "array_bat_begin_access", {ret_type = Ptr batcher_struct;
                                arg_types = stt [Ptr arr_bat_struct; Sint32;];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [];};
     "array_bat_end_access", {ret_type = Void;
                              arg_types = stt [Ptr arr_bat_struct;];
                              extra_ptr_types = [];
                              lemmas_before = [];
                              lemmas_after = [];};
     "array_lcc_init", {ret_type = Void;
                        arg_types = stt [Ptr arr_lcc_struct;];
                        extra_ptr_types = [];
                        lemmas_before = [];
                        lemmas_after = [
                          (fun params ->
                             the_array_lcc_is_local := true;
                             "");];};
     "array_lcc_begin_access", {ret_type = Ptr lcore_conf_struct;
                                arg_types = stt [Ptr arr_lcc_struct; Sint32;];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [
                                  (fun params ->
                                     "last_lcc = " ^ params.ret_name ^ ";\n");
                                  (fun params ->
                                     if params.is_tip then
                                       "//@ open lcore_confp(_, last_lcc);"
                                     else "");
                                  (fun params ->
                                     if params.is_tip then "" else
                                       "//@ open lcore_confp(_, last_lcc);");
                                ];};
     "array_lcc_end_access", {ret_type = Void;
                              arg_types = stt [Ptr arr_lcc_struct;];
                              extra_ptr_types = ["returned_cell",
                                                lcore_conf_struct];
                              lemmas_before = [
                               tx_bl "close lcore_confp(_, last_lcc);";
                              ];
                              lemmas_after = [];};
     "array_rq_begin_access", {ret_type = Ptr lcore_rx_queue_struct;
                               arg_types = stt [Ptr arr_rq_struct; Sint32;];
                               extra_ptr_types = [];
                               lemmas_before = [];
                               lemmas_after = [
                                 (fun params ->
                                    "last_rq = " ^ params.ret_name ^ ";\n");
                                 (fun params ->
                                    "//@ open rx_queuep(_, last_rq);");
                               ];};
     "array_rq_end_access", {ret_type = Void;
                             arg_types = stt [Ptr arr_rq_struct;];
                             extra_ptr_types = ["returned_rq_cell",
                                                lcore_rx_queue_struct];
                             lemmas_before = [
                               tx_bl "close rx_queuep(_, last_rq);";
                             ];
                             lemmas_after = [];};
     "array_u16_begin_access", {ret_type = Ptr Uint16;
                                arg_types = stt [Ptr arr_u16_struct; Sint32;];
                                extra_ptr_types = [];
                                lemmas_before = [];
                                lemmas_after = [
                                  (fun params ->
                                     if params.is_tip then
                                       "//@ close some_u16p(" ^ params.ret_val ^ ");"
                                     else "");
                                  (fun params ->
                                     if params.is_tip then
                                       "//@ close some_u16p(" ^ params.ret_name ^ ");"
                                     else "")];};
     "array_u16_end_access", {ret_type = Void;
                              arg_types = stt [Ptr arr_u16_struct;];
                              extra_ptr_types = ["returned_u16_cell",
                                                 Uint16];
                              lemmas_before = [];
                              lemmas_after = [];};
     "batcher_push", {ret_type = Void;
                      arg_types = stt [Ptr batcher_struct; Ptr rte_mbuf_struct;];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [];};
     "batcher_take_all", {ret_type = Void;
                          arg_types = stt [Ptr batcher_struct;
                                       Ptr (Ptr (Ptr rte_mbuf_struct));
                                       Ptr Sint32];
                          extra_ptr_types = [];
                          lemmas_before = [];
                          lemmas_after = [];};
     "batcher_empty", {ret_type = Void;
                       arg_types = stt [Ptr batcher_struct;];
                       extra_ptr_types = [];
                       lemmas_before = [];
                       lemmas_after = [];};
     "batcher_full", {ret_type = Sint32;
                      arg_types = stt [Ptr batcher_struct;];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [];};
     "batcher_is_empty", {ret_type = Sint32;
                          arg_types = stt [Ptr batcher_struct;];
                          extra_ptr_types = [];
                          lemmas_before = [];
                          lemmas_after = [];};
     "received_packet", {ret_type = Void;
                         arg_types = stt [Ir.Uint8; Ptr rte_mbuf_struct;];
                         extra_ptr_types = ["user_buf_addr", user_buf_struct];
                         lemmas_before = [];
                         lemmas_after = [(fun _ -> "a_packet_received = true;\n");
                                         (fun params ->
                                            let recv_pkt =
                                              (List.nth_exn params.args 1)
                                            in
                                            (copy_user_buf "the_received_packet"
                                               recv_pkt) ^ "\n" ^
                                            "received_on_port = (" ^
                                            recv_pkt ^ ")->port;\n" ^
                                            "received_packet_type = (" ^
                                            recv_pkt ^ ")->packet_type;");
                                           ];};
     "send_single_packet", {ret_type = Ir.Sint32;
                            arg_types = stt [Ptr rte_mbuf_struct; Ir.Uint8];
                            extra_ptr_types = ["user_buf_addr", user_buf_struct];
                            lemmas_before = [];
                            lemmas_after = [(fun _ -> "a_packet_sent = true;\n");
                                            (fun params ->
                                               let sent_pkt =
                                                 (List.nth_exn params.args 0)
                                               in
                                               (copy_user_buf "sent_packet"
                                                  sent_pkt) ^ "\n" ^
                                               "sent_on_port = " ^
                                               (List.nth_exn params.args 1) ^
                                               ";\n" ^
                                               "sent_packet_type = (" ^
                                               sent_pkt ^ ")->packet_type;");];};
     "rte_pktmbuf_free", {ret_type = Void;
                          arg_types = stt [Ptr rte_mbuf_struct;];
                          extra_ptr_types = [];
                          lemmas_before = [];
                          lemmas_after = [];}
    ]

let fixpoints =
  String.Map.of_alist_exn [
    "nat_int_fp", {Ir.v=Bop(And,
                            {v=Bop(Le,{v=Int 0;t=Sint32},{v=Str_idx({v=Id "Arg0";t=Unknown},"idid");t=Unknown});t=Unknown},
                            {v=Bop(Lt,{v=Str_idx({v=Id "Arg0";t=Unknown},"idid");t=Unknown},
                                   {v=Int 2;t=Sint32});t=Unknown});t=Boolean};
    "nat_ext_fp", {v=Bop(And,
                         {v=Bop(And,
                                {v=Bop(Le,
                                       {v=Int 0;t=Sint32},
                                       {v=Str_idx({v=Id "Arg1";t=Unknown},"edid");t=Unknown});
                                 t=Unknown},
                                {v=Bop(Lt,
                                       {v=Str_idx({v=Id "Arg1";t=Unknown},"edid");t=Unknown},
                                       {v=Int 2;t=Sint32});t=Unknown});
                          t=Boolean},
                         {v=Bop(Eq,
                                {v=Str_idx({v=Id "Arg1";t=Unknown},"edid");t=Unknown},
                                {v=Bop(Add,
                                       {v=Id "Arg0";t=Sint32},
                                       {v=Id "Arg2";t=Sint32});t=Unknown});
                          t=Boolean});
                   t=Boolean};
    "ikc", {v=Struct ("int_k",
                      [{name="isp";value={v=Id "Arg0";t=Unknown}};
                       {name="dp";value={v=Id "Arg1";t=Unknown}};
                       {name="isip";value={v=Id "Arg2";t=Unknown}};
                       {name="dip";value={v=Id "Arg3";t=Unknown}};
                       {name="idid";value={v=Id "Arg4";t=Unknown}};
                       {name="prtc";value={v=Id "Arg5";t=Unknown}}]);
           t=Unknown};
    "ekc", {v=Struct ("ext_k",
                      [{name="esp";value={v=Id "Arg0";t=Unknown}};
                       {name="dp";value={v=Id "Arg1";t=Unknown}};
                       {name="esip";value={v=Id "Arg2";t=Unknown}};
                       {name="dip";value={v=Id "Arg3";t=Unknown}};
                       {name="edid";value={v=Id "Arg4";t=Unknown}};
                       {name="prtc";value={v=Id "Arg5";t=Unknown}}]);
           t=Unknown};
    "integer", {v=Bop(Eq,{v=Id "Arg0";t=Unknown},{v=Id "Arg1";t=Unknown});t=Boolean};
    "flow_int_device_id", {v=Bop(Eq,{v=Str_idx({v=Id "Arg0";t=Unknown},"int_device_id");t=Unknown},
                                 {v=Id "Arg1";t=Unknown}); t=Boolean};
    "flow_ext_device_id", {v=Bop(Eq,{v=Str_idx({v=Id "Arg0";t=Unknown},"ext_device_id");t=Unknown},
                                 {v=Id "Arg1";t=Unknown}); t=Boolean};
    "flwc", {v=Struct ("flw",
                       [{name="ik";value={v=Id "Arg0";t=Unknown}};
                        {name="ek";value={v=Id "Arg1";t=Unknown}};
                        {name="isp";value={v=Id "Arg2";t=Unknown}};
                        {name="esp";value={v=Id "Arg3";t=Unknown}};
                        {name="dp";value={v=Id "Arg4";t=Unknown}};
                        {name="isip";value={v=Id "Arg5";t=Unknown}};
                        {name="esip";value={v=Id "Arg6";t=Unknown}};
                        {name="dip";value={v=Id "Arg7";t=Unknown}};
                        {name="idid";value={v=Id "Arg8";t=Unknown}};
                        {name="edid";value={v=Id "Arg9";t=Unknown}};
                        {name="prtc";value={v=Id "Arg10";t=Unknown}};
                       ]);t=Unknown};
    "flw_get_ik", {v=Str_idx({v=Id "Arg0";t=Unknown},"ik");t=Unknown};
    "flw_get_ek", {v=Str_idx({v=Id "Arg0";t=Unknown},"ek");t=Unknown};
  ]

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = (In_channel.read_all "preamble.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  uint32_t external_ip = 0;\n\
                  struct lcore_conf *last_lcc;\n\
                  struct lcore_rx_queue *last_rq;\n\
                  uint8_t received_on_port;\n\
                  uint32_t received_packet_type;\n\
                  struct user_buf the_received_packet;\n\
                  bool a_packet_received = false;\n\
                  struct user_buf sent_packet;\n\
                  uint8_t sent_on_port;\n\
                  uint32_t sent_packet_type;\n\
                  bool a_packet_sent = false;\n"
  let fun_types = fun_types
  let fixpoints = fixpoints
  let boundary_fun = "loop_invariant_produce"
  let finishing_fun = "loop_invariant_consume"
  let eventproc_iteration_begin = "loop_invariant_produce"
  let eventproc_iteration_end = "loop_invariant_consume"
  let user_check_for_complete_iteration =
    (In_channel.read_all "forwarding_property.tmpl")
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

