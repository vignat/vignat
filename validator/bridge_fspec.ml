
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

let capture_chain ch_name ptr_num {args;tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen ch_name) ^ ", " ^
  (List.nth_exn args ptr_num) ^ ");\n"

let capture_a_chain name {tmp_gen;_} =
  "//@ assert double_chainp(?" ^ (tmp_gen name) ^", _);\n"

let capture_a_map t name {tmp_gen;_} =
  "//@ assert mapp<" ^ t ^ ">(_, _, _, mapc(_,?" ^ (tmp_gen name) ^ "));\n"

let capture_a_vector t name {tmp_gen;_} =
  "//@ assert vectorp<" ^ t ^ ">(_, _, ?" ^ (tmp_gen name) ^ ");\n"

let map_struct = Ir.Str ("Map", [])
let vector_struct = Ir.Str ( "Vector", [] )
let dchain_struct = Ir.Str ( "DoubleChain", [] )
let ether_addr_struct = Ir.Str ( "ether_addr", ["a", Uint8;
                                                "b", Uint8;
                                                "c", Uint8;
                                                "d", Uint8;
                                                "e", Uint8;
                                                "f", Uint8;])
let static_key_struct = Ir.Str ( "StaticKey", ["addr", ether_addr_struct;
                                               "device", Uint8] )
let dynamic_entry_struct = Ir.Str ( "DynamicEntry", ["addr", ether_addr_struct;
                                                     "device", Uint8] )
let ether_hdr_struct = Ir.Str ("ether_hdr", ["d_addr", ether_addr_struct;
                                             "s_addr", ether_addr_struct;
                                             "ether_type", Uint16;])

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
(* FIXME: for bridge only ether_hdr is needed, the other two are here,
   just because rte_stubs.c dumps them for the other NF (NAT), and validator
   ensures we read everything dumped.*)
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
     "bridge_loop_invariant_consume", {ret_type = Void;
                                       arg_types = stt
                                           [Ptr (Ptr dchain_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Uint32;
                                            Uint32];
                                       extra_ptr_types = [];
                                       lemmas_before = [
                                         (fun {args;_} ->
                                            "/*@ close bridge_loop_invariant(*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", " ^
                                            (List.nth_exn args 5) ^ ", " ^
                                            (List.nth_exn args 6) ^ "); @*/");];
                                       lemmas_after = [];};
     "bridge_loop_invariant_produce", {ret_type = Void;
                                       arg_types = stt
                                           [Ptr (Ptr dchain_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Uint32;
                                            Ptr Uint32];
                                       extra_ptr_types = [];
                                       lemmas_before = [];
                                       lemmas_after = [
                                         (fun {args;_} ->
                                            "/*@ open bridge_loop_invariant (*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", " ^
                                            (List.nth_exn args 5) ^ ", *" ^
                                            (List.nth_exn args 6) ^ "); @*/");];};
     "dchain_allocate", {ret_type = Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                             "{\n\
                              assert vectorp<dynenti>(_, _, ?allocated_vector);\n\
                              }";
                           tx_l "index_range_of_empty(65536, 0);";];};
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
                                 arg_types = stt [Ptr dchain_struct;
                                                  Sint32; Uint32;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {args;tmp_gen;_} ->
                                      "/*@ {\n\
                                        assert map_vec_chain_coherent<\
                                       ether_addri,dynenti>(?" ^
                                      (tmp_gen "cur_map") ^ ", ?" ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^
                                      ");\n\
                                       mvc_coherent_same_len(" ^
                                      (tmp_gen "cur_map") ^ ", " ^
                                      (tmp_gen "cur_vec") ^ ", " ^
                                      (tmp_gen "cur_ch") ^ ");\n} @*/");
                                   (fun {args;tmp_gen;_} ->
                                      "//@ rejuvenate_keeps_high_bounded(" ^
                                      (tmp_gen "cur_ch") ^
                                      ", " ^ (List.nth_exn args 1) ^
                                      ", " ^ (List.nth_exn args 2) ^
                                      ");\n");];
                                 lemmas_after = [
                                   (fun params ->
                                      "/*@ if (" ^ params.ret_name ^
                                      " != 0) { \n" ^
                                      "assert map_vec_chain_coherent<ether_addri,\
                                       dynenti>(?cur_map,?cur_vec,?cur_ch);\n" ^
                                      "mvc_rejuvenate_preserves_coherent(cur_map,\
                                       cur_vec, cur_ch, " ^
                                      (List.nth_exn params.args 1) ^ ", "
                                      ^ (List.nth_exn params.args 2) ^ ");\n\
                                       rejuvenate_preserves_index_range(cur_ch," ^
                                      (List.nth_exn params.args 1) ^ ", " ^
                                      (List.nth_exn params.args 2) ^ ");\n}@*/");
                                   (fun params ->
                                      "int the_index_rejuvenated = " ^
                                      (List.nth_exn params.args 1) ^ ";\n");
                                 ];};
     "expire_items_single_map", {ret_type = Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Ptr vector_struct;
                                                  Ptr map_struct;
                                                  Fptr "entry_extract_key";
                                                  Fptr "entry_pack_key";
                                                  Uint32];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   tx_bl
                                     "produce_function_pointer_chunk \
                                      entry_extract_key<ether_addri,\
                                      dynenti>(dyn_entry_get_addr)\
                                      (ether_addrp,dynamic_entryp,\
                                      dynamic_entry_barep,\
                                      dynentry_right_offsets,\
                                      dynentry_get_addr_fp)(a, b) \
                                      {\
                                      call();\
                                      }";
                                   tx_bl
                                     "produce_function_pointer_chunk \
                                      entry_pack_key<ether_addri,\
                                      dynenti>(dyn_entry_retrieve_addr)\
                                      (ether_addrp,dynamic_entryp,\
                                      dynamic_entry_barep,\
                                      dynentry_right_offsets,\
                                      dynentry_get_addr_fp)(a, b) \
                                      {\
                                      call();\
                                      }\n\
                                     ";
                                   (fun {tmp_gen;_} ->
                                      "//@ assert mapp<stat_keyi>(?" ^
                                      (tmp_gen "stmp") ^ ", _, _, _);\n" ^
                                      "//@ close hide_mapp<stat_keyi>(" ^
                                      (tmp_gen "stmp") ^ ");\n");
                                 ];
                                 lemmas_after = [];};
     "map_allocate", {ret_type = Sint32;
                      arg_types = stt [Fptr "map_keys_equality";
                                       Fptr "map_key_hash";
                                       Sint32;
                                       Ptr (Ptr map_struct)];
                      extra_ptr_types = [];
                      lemmas_before = [
                        (fun {args;_} ->
                           "/*@ if (" ^ (List.nth_exn args 0) ^
                           " == static_key_eq) {\n" ^
                           "produce_function_pointer_chunk \
                            map_keys_equality<stat_keyi>(static_key_eq)\
                            (static_keyp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<stat_keyi>(static_key_hash)\
                            (static_keyp, st_key_hash)(a) \
                            {\
                            call();\
                            }\n\
                            } else {\n\
                            produce_function_pointer_chunk \
                            map_keys_equality<ether_addri>(ether_addr_eq)\
                            (ether_addrp)(a, b) \
                            {\
                            call();\
                            }\n\
                            produce_function_pointer_chunk \
                            map_key_hash<ether_addri>(ether_addr_hash)\
                            (ether_addrp, eth_addr_hash)(a) \
                            {\
                            call();\
                            }\n\
                            } @*/ \n");];
                      lemmas_after = [
                        (fun params ->
                           "/*@ if (" ^ (List.nth_exn params.args 0) ^
                           " == static_key_eq) {\n\
                            assert [?" ^ (params.tmp_gen "imkest") ^
                           "]is_map_keys_equality(static_key_eq,\
                            static_keyp);\n\
                            close [" ^ (params.tmp_gen "imkest") ^
                           "]hide_is_map_keys_equality(static_key_eq, \
                            static_keyp);\n\
                            assert [?" ^ (params.tmp_gen "imkhst") ^
                           "]is_map_key_hash(static_key_hash,\
                            static_keyp, st_key_hash);\n\
                            close [" ^ (params.tmp_gen "imkhst") ^
                           "]hide_is_map_key_hash(static_key_hash, \
                            static_keyp, st_key_hash);\n\
                            } else {\n\
                            assert [?" ^ (params.tmp_gen "imkedy") ^
                           "]is_map_keys_equality(ether_addr_eq,\
                            ether_addrp);\n\
                            close [" ^ (params.tmp_gen "imkedy") ^
                           "]hide_is_map_keys_equality(ether_addr_eq, \
                            ether_addrp);\n\
                            assert [?" ^ (params.tmp_gen "imkhdy") ^
                           "]is_map_key_hash(ether_addr_hash,\
                            ether_addrp, eth_addr_hash);\n\
                            close [" ^ (params.tmp_gen "imkhdy") ^
                           "]hide_is_map_key_hash(ether_addr_hash, \
                            ether_addrp, eth_addr_hash);\n\
                            } @*/")];};
     "map_get", {ret_type = Sint32;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic [Ptr ether_addr_struct;
                                       Ptr static_key_struct];
                              Static (Ptr Sint32)];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun {arg_types;tmp_gen;args;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("ether_addr", _)) ->
                        "//@ assert mapp<stat_keyi>(?" ^ (tmp_gen "stm_ptr") ^
                        ", _, _, _);\n\
                         //@ close hide_mapp<stat_keyi>(" ^
                        (tmp_gen "stm_ptr") ^
                        ");\n" ^
                        "//@ assert ether_addrp(" ^ (List.nth_exn args 1) ^
                        ", ?" ^ (tmp_gen "dk") ^ ");"
                      | Ptr (Str ("StaticKey", _)) ->
                        "//@ assert mapp<ether_addri>(?" ^ (tmp_gen "eam_ptr") ^
                        ", _, _, _);\n\
                         //@ close hide_mapp<ether_addri>(" ^
                        (tmp_gen "eam_ptr") ^
                        ");"
                      | _ -> "#error unexpected key type");
                   capture_a_chain "dh";
                   capture_a_map "ether_addri" "dm";
                   capture_a_vector "dynenti" "dv";
                 ];
                 lemmas_after = [
                   (fun {ret_name;arg_types;tmp_gen;_} ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("ether_addr", _)) ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         mvc_coherent_map_get_bounded(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "dk") ^
                        ");\n\
                         } @*/"
                      | _ -> "");];};
     "map_put", {ret_type = Void;
                 arg_types = stt [Ptr map_struct;
                                  Ptr Void;
                                  Sint32];
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
     "rte_pktmbuf_free", {ret_type = Void;
                          arg_types = stt [Ptr rte_mbuf_struct;];
                          extra_ptr_types = [];
                          lemmas_before = [];
                          lemmas_after = [];};
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
     "start_time", {ret_type = Uint32;
                    arg_types = [];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
     "vector_allocate", {ret_type = Sint32;
                         arg_types = stt [Sint32;
                                          Sint32;
                                          Fptr "vector_init_elem";
                                          Ptr (Ptr vector_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [
                           tx_bl
                             "if (stat_vec_allocated) {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<dynenti>(init_nothing)\
                              (dynamic_entryp, sizeof(struct DynamicEntry))(a) \
                              {\
                              call();\
                              }\n
                              } else {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<stat_keyi>(init_nothing_st)\
                              (static_keyp, sizeof(struct StaticKey))(a) \
                              {\
                              call();\
                              }\n\
                              }";
                         ];
                         lemmas_after = [
                           (fun _ ->
                              "if (!stat_vec_allocated)\
                               stat_vec_allocated = true;");];};
     "vector_borrow", {ret_type = Ptr Void;
                       arg_types = stt [Ptr vector_struct;
                                        Sint32];
                       extra_ptr_types = [];
                       lemmas_before = [];
                       lemmas_after = [];};
     "vector_return", {ret_type = Void;
                       arg_types = stt [Ptr vector_struct;
                                        Sint32;
                                        Ptr Void];
                       extra_ptr_types = [];
                       lemmas_before = [];
                       lemmas_after = [];};]

let fixpoints =
  String.Map.of_alist_exn []

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = (In_channel.read_all "preamble.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  uint8_t received_on_port;\n\
                  uint32_t received_packet_type;\n\
                  struct user_buf the_received_packet;\n\
                  bool a_packet_received = false;\n\
                  struct user_buf sent_packet;\n\
                  uint8_t sent_on_port;\n\
                  uint32_t sent_packet_type;\n\
                  bool a_packet_sent = false;\n"
                 ^
                 "/*@ //TODO: this hack should be \
                  converted to a system \n\
                  assume(sizeof(struct DynamicEntry) == 7);\n@*/\n\
                  /*@\
                  assume(sizeof(struct StaticKey) == 7);\n@*/\n"
                 ^
                 "/*@ assume(ether_addr_eq != static_key_eq); @*/\n"
                 ^
                 "bool stat_vec_allocated = false;\n"
  let fun_types = fun_types
  let fixpoints = fixpoints
  let boundary_fun = "bridge_loop_invariant_produce"
  let finishing_fun = "bridge_loop_invariant_consume"
  let eventproc_iteration_begin = "bridge_loop_invariant_produce"
  let eventproc_iteration_end = "bridge_loop_invariant_consume"
  let user_check_for_complete_iteration =
    "" (*In_channel.read_all "forwarding_property.tmpl"*)
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

