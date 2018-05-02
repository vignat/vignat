open Str
open Core
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
  "//@ assert mapp<" ^ t ^ ">(_, _, _, _, mapc(_,?" ^ (tmp_gen name) ^ ", _));\n"

let capture_a_vector t name {tmp_gen;_} =
  "//@ assert vectorp<" ^ t ^ ">(_, _, ?" ^ (tmp_gen name) ^ ", _);\n"

let rec self_dereference tterm tmpgen =
  match tterm.v with
  | Id x -> ("//@ assert *&" ^ x ^ "|-> ?" ^
             (tmpgen ("pp" ^ x) ^ ";"),
             {v=Id (tmpgen ("pp" ^ x));t=tterm.t})
  | Str_idx (x,fname) ->
    let (binding, x) = self_dereference x tmpgen in
    (binding,{v=Str_idx (x,fname);t=tterm.t})
  | Addr x ->
    let (binding, x) = self_dereference x tmpgen in
    (binding,{v=Addr x;t=tterm.t})
  | Deref x ->
    let (binding, x) = self_dereference x tmpgen in
    (binding,{v=Deref x;t=tterm.t})
  | _ -> failwith ("unhandled in self_deref: " ^ (render_tterm tterm))

let rec innermost_dereference tterm tmpgen =
  match tterm.v with
  | Str_idx ({v=Deref {v=Id x;t=_};t=_},fname) ->
    let tmpname = (tmpgen ("stp" ^ x ^ "_" ^ fname)) in
    ("//@ assert " ^ (render_tterm tterm) ^ " |-> ?" ^
     tmpname ^ ";",
     {v=Id tmpname;t=tterm.t})
  | Addr x ->
    let (binding, x) = innermost_dereference x tmpgen in
    (binding, {v=Addr x;t=tterm.t})
  | Deref x ->
    let (binding, x) = innermost_dereference x tmpgen in
    (binding, {v=Deref x;t=tterm.t})
  | Str_idx (x,fname) ->
    let (binding, x) = innermost_dereference x tmpgen in
    (binding, {v=Str_idx (x,fname);t=tterm.t})
  | _ -> failwith ("unhandled in inn_deref: " ^ (render_tterm tterm))

let generate_2step_dereference tterm tmpgen =
  let (binding1,x) = self_dereference tterm tmpgen in
  let (binding2,x) = innermost_dereference x tmpgen in
  ([binding1;binding2],x)

let hide_the_other_mapp {arg_types;tmp_gen;args;arg_exps;_} =
  match List.nth_exn arg_types 1 with
  | Ptr (Str ("ether_addr", _)) ->
    "//@ assert mapp<stat_keyi>(?" ^ (tmp_gen "stm_ptr") ^
    ", _, _, _, ?" ^ (tmp_gen "stm") ^ ");\n\
                                        //@ close hide_mapp<stat_keyi>(" ^
    (tmp_gen "stm_ptr") ^
    ", static_keyp, st_key_hash, _," ^
    (tmp_gen "stm") ^ ");\n"
  | Ptr (Str ("StaticKey", _)) ->
    "//@ assert mapp<ether_addri>(?" ^ (tmp_gen "eam_ptr") ^
    ", _, _, _, ?" ^ (tmp_gen "dym") ^ ");\n\
                                        //@ close hide_mapp<ether_addri>(" ^
    (tmp_gen "eam_ptr") ^
    ", ether_addrp, eth_addr_hash, _, " ^
    (tmp_gen "dym") ^
    ");\n"
  | _ -> "#error unexpected key type"

let reveal_the_other_mapp : lemma = fun {arg_types;tmp_gen;args;_} ->
  match List.nth_exn arg_types 1 with
  | Ptr (Str ("ether_addr", _)) ->
    "//@ open hide_mapp<stat_keyi>(" ^
    (tmp_gen "stm_ptr") ^ ", static_keyp, st_key_hash, _," ^
    (tmp_gen "stm") ^ ");\n"
  | Ptr (Str ("StaticKey", _)) ->
    "//@ open hide_mapp<ether_addri>(" ^
    (tmp_gen "eam_ptr") ^ ", ether_addrp, eth_addr_hash, _," ^
    (tmp_gen "dym") ^ ");"
  | _ -> "#error unexpected key type"

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
                                               "device", Uint16] )
let dynamic_value_struct = Ir.Str ( "DynamicValue", ["device", Uint16] )
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
let stub_mbuf_content_struct = Ir.Str ( "stub_mbuf_content",
                                        ["ether", ether_hdr_struct;
                                         "ipv4", ipv4_hdr_struct;
                                         "tcp", tcp_hdr_struct;])

let rte_mempool_struct = Ir.Str ( "rte_mempool", [] )
let rte_mbuf_struct = Ir.Str ( "rte_mbuf",
                               ["buf_addr", Ptr stub_mbuf_content_struct;
                                "buf_iova", Uint64;
                                "data_off", Uint16;
                                "refcnt", Uint16;
                                "nb_segs", Uint16;
                                "port", Uint16;
                                "ol_flags", Uint64;
                                "packet_type", Uint32;
                                "pkt_len", Uint32;
                                "data_len", Uint16;
                                "vlan_tci", Uint16;
                                "hash", Uint32;
                                "vlan_tci_outer", Uint16;
                                "buf_len", Uint16;
                                "timestamp", Uint64;
                                "udata64", Uint64;
                                (*"pool", Ptr rte_mempool_struct;*)
                                (*"next", Ptr Void;*)
                                "tx_offload", Uint64;
                                "priv_size", Uint16;
                                "timesync", Uint16;
                                "seqn", Uint32] )

let copy_stub_mbuf_content var_name ptr =
  ("struct stub_mbuf_content* tmp_ub_ptr" ^ var_name ^
   " = (" ^ ptr ^ ")->buf_addr;\n") ^
  deep_copy
    {Ir.name=var_name;
     Ir.value={v=Deref {v=Ir.Id ("tmp_ub_ptr" ^ var_name);
                        t=Ptr stub_mbuf_content_struct};
               t=stub_mbuf_content_struct}}

(* VeriFast's C parser is quite limited, so simplify stuff... this is very brittle since it does no lookbehind to avoid accidents *)
let rec simplify_c_string str =
  let str0 = Str.global_replace (Str.regexp "\\*&") "" str in (* *&a  ==>  a *)
  let str0 = Str.global_replace (Str.regexp "\\*(&\\([^)]+\\))") "\\1" str0 in (* * (&a)  ==>  a *)
  let str0 = Str.global_replace (Str.regexp "&(\\([^)]+\\))->\\([^)]+\\)") "\\1.\\2" str0 in (* &a->b  ==>  a.b *)
  let str0 = Str.global_replace (Str.regexp "(&(\\([^)]+\\)))->\\([^)]+\\)") "\\1.\\2" str0 in (* (&a)->b  ==>  a.b *)
  let str0 = Str.global_replace (Str.regexp "(\\*\\([^)]+\\).\\([^)]+\\)") "\\1->\\2" str0 in (* ( *a ).b  ==>  a->b *)
  if str = str0 then str else simplify_c_string str0 (* find a fixpoint *)

let fun_types =
  String.Map.of_alist_exn
    ["current_time", {ret_type = Static Sint64;
                      arg_types = [];
                      extra_ptr_types = [];
                      lemmas_before = [];
                      lemmas_after = [
                        (fun params ->
                           "int64_t now = " ^ (params.ret_name) ^ ";\n")];};
     "bridge_loop_invariant_consume", {ret_type = Static Void;
                                       arg_types = stt
                                           [Ptr (Ptr dchain_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Uint32;
                                            Sint64;
                                            Uint16];
                                       extra_ptr_types = [];
                                       lemmas_before = [
                                         (fun {args;_} ->
                                            "/*@ close bridge_loop_invariant(*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", *" ^
                                            (List.nth_exn args 5) ^ ", " ^
                                            (List.nth_exn args 6) ^ ", " ^
                                            (List.nth_exn args 7) ^ ", " ^
                                            (List.nth_exn args 8) ^ "); @*/");];
                                       lemmas_after = [];};
     "bridge_loop_invariant_produce", {ret_type = Static Void;
                                       arg_types = stt
                                           [Ptr (Ptr dchain_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr vector_struct);
                                            Ptr (Ptr map_struct);
                                            Ptr (Ptr vector_struct);
                                            Uint32;
                                            Ptr Sint64;
                                            Uint16];
                                       extra_ptr_types = [];
                                       lemmas_before = [];
                                       lemmas_after = [
                                         (fun {args;_} ->
                                            "/*@ open bridge_loop_invariant (*" ^
                                            (List.nth_exn args 0) ^ ", *" ^
                                            (List.nth_exn args 1) ^ ", *" ^
                                            (List.nth_exn args 2) ^ ", *" ^
                                            (List.nth_exn args 3) ^ ", *" ^
                                            (List.nth_exn args 4) ^ ", *" ^
                                            (List.nth_exn args 5) ^ ", " ^
                                            (List.nth_exn args 6) ^ ", *" ^
                                            (List.nth_exn args 7) ^ ", " ^
                                            (List.nth_exn args 8) ^ "); @*/");
                                         (fun {tmp_gen;_} ->
                                            "\n/*@ {\n\
                                             assert mapp<ether_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                                            ", _));\n\
                                             assert vectorp<ether_addri>(_, _, ?" ^ (tmp_gen "dv") ^
                                            ", _);\n\
                                             assert vectorp<uint16_t>(_, _, ?" ^ (tmp_gen "dv_init") ^
                                            ", _);\n\
                                             assert map_vec_chain_coherent<ether_addri>(" ^
                                            (tmp_gen "dm") ^ ", " ^
                                            (tmp_gen "dv") ^ ", ?" ^
                                            (tmp_gen "dh") ^
                                            ");\n\
                                             mvc_coherent_same_len<ether_addri>(" ^ (tmp_gen "dm") ^
                                            ", " ^ (tmp_gen "dv") ^
                                            ", " ^ (tmp_gen "dh") ^
                                            ");\n\
                                             assert mapp<ether_addri>(_, _, _, _, ?" ^ (tmp_gen "dm_full") ^
                                            ");\n\
                                            initial_dyn_map = " ^ (tmp_gen "dm_full") ^
                                            ";\ninitial_dyn_val_vec = " ^ (tmp_gen "dv_init") ^
                                            ";\ninitial_dyn_key_vec = " ^ (tmp_gen "dv") ^
                                            ";\ninitial_chain = " ^ (tmp_gen "dh") ^
                                            ";\n} @*/");
                                       ];};
     "dchain_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32; Ptr (Ptr dchain_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nonzero
                             "{\n\
                              assert vectorp<ether_addri>(_, _, ?allocated_vector, _);\n\
                              empty_map_vec_dchain_coherent\
                              <ether_addri>(allocated_vector);\n\
                              }";
                           tx_l "index_range_of_empty(65536, 0);";];};
     "dchain_allocate_new_index", {ret_type = Static Sint32;
                                   arg_types = stt [Ptr dchain_struct; Ptr Sint32; Uint32;];
                                   extra_ptr_types = [];
                                   lemmas_before = [
                                     capture_chain "cur_ch" 0;
                                   ];
                                   lemmas_after = [
                                     (fun {args;_} ->
                                        "time_for_allocated_index = " ^ (List.nth_exn args 2) ^
                                        ";\n");
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
                                        "the_index_allocated = *" ^
                                        (List.nth_exn params.args 1) ^ ";\n");
                                     on_rez_nz
                                       (fun {args;tmp_gen;_} ->
                                          "{\n\
                                           assert map_vec_chain_coherent<\
                                           ether_addri>(?" ^
                                          (tmp_gen "cur_map") ^ ", ?" ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^
                                          ");\n\
                                           mvc_coherent_alloc_is_halfowned<ether_addri>(" ^
                                          (tmp_gen "cur_map") ^ ", " ^
                                          (tmp_gen "cur_vec") ^ ", " ^
                                          (tmp_gen "cur_ch") ^ ", *" ^
                                          (List.nth_exn args 1) ^ ");\n}");
                                   ];};
     "dchain_rejuvenate_index", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Sint32; Uint32;];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun {args;tmp_gen;_} ->
                                      "/*@ {\n\
                                        assert map_vec_chain_coherent<\
                                       ether_addri>(?" ^
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
                                      "assert map_vec_chain_coherent<ether_addri>\
                                       (?cur_map,?cur_vec,?cur_ch);\n" ^
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
     "expire_items_single_map", {ret_type = Static Sint32;
                                 arg_types = stt [Ptr dchain_struct;
                                                  Ptr vector_struct;
                                                  Ptr map_struct;
                                                  Uint32];
                                 extra_ptr_types = [];
                                 lemmas_before = [
                                   (fun {tmp_gen;_} ->
                                      "//@ assert mapp<stat_keyi>(?" ^
                                      (tmp_gen "stmp") ^ ", _, _, _, ?stm);\n" ^
                                      "//@ close hide_mapp<stat_keyi>(" ^
                                      (tmp_gen "stmp") ^ ", static_keyp,\
                                                          st_key_hash,\
                                                          _,\
                                                          stm);\n");
                                   (fun {tmp_gen;args;_} ->
                                      "//@ assert double_chainp(?" ^
                                      (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 0) ^ ");\n" ^
                                      "//@ expire_olds_keeps_high_bounded(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^ (List.nth_exn args 3) ^ ");\n");
                                   (fun {args;tmp_gen;_} ->
                                      "/*@ {\n\
                                       expire_preserves_index_range(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      ");\n\
                                       length_nonnegative(\
                                       dchain_get_expired_indexes_fp(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      "));\n\
                                       if (length(dchain_get_expired_indexes_fp(" ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      ")) > 0 ) {\n\
                                       expire_old_dchain_nonfull\
                                       (" ^ (List.nth_exn args 0) ^ ", " ^
                                      (tmp_gen "cur_ch") ^ ", " ^
                                      (List.nth_exn args 3) ^
                                      ");\n\
                                       }} @*/");
                                 ];
                                 lemmas_after = [
                                   (fun {tmp_gen;_} ->
                                      "//@ open hide_mapp<stat_keyi>(" ^
                                      (tmp_gen "stmp") ^ ", static_keyp,\
                                                          st_key_hash,\
                                                          _,\
                                                          stm);\n");
                                   (fun {tmp_gen;_} ->
                                      "\n/*@ {\n\
                                       assert mapp<ether_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                                      ", _));\n\
                                       assert vectorp<ether_addri>(_, _, ?" ^ (tmp_gen "dv") ^
                                      ", _);\n\
                                       assert map_vec_chain_coherent<ether_addri>(" ^
                                      (tmp_gen "dm") ^ ", " ^
                                      (tmp_gen "dv") ^ ", ?" ^
                                      (tmp_gen "dh") ^
                                      ");\n\
                                       assert vectorp<uint16_t>(_, _, ?" ^ (tmp_gen "dv_exprnd") ^
                                      ", _);\n\
                                       assert mapp<ether_addri>(_, _, _, _, ?" ^ (tmp_gen "dm_full") ^
                                      ");\n\
                                       exprnd_dyn_map = " ^ (tmp_gen "dm_full") ^
                                      ";\nexprnd_dyn_val_vec = " ^ (tmp_gen "dv_exprnd") ^
                                      ";\nexprnd_chain = " ^ (tmp_gen "dh") ^
                                      ";\nmvc_coherent_same_len<ether_addri>(" ^
                                      (tmp_gen "dm") ^ ", " ^
                                      (tmp_gen "dv") ^ ", " ^
                                      (tmp_gen "dh") ^ ");\n} @*/"
                                         );
                                 ];};
     "map_allocate", {ret_type = Static Sint32;
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
     "map_get", {ret_type = Static Sint32;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["ether_addr", Ptr ether_addr_struct;
                                       "StaticKey", Ptr static_key_struct];
                              Static (Ptr Sint32)];
                 extra_ptr_types = [];
                 lemmas_before = [
                   hide_the_other_mapp;
                   (fun ({arg_types;tmp_gen;args;arg_exps;_} as params) ->
                      match List.nth_exn arg_types 1 with
                      | Ptr (Str ("ether_addr", _)) ->
                        let (bindings,expr) =
                          generate_2step_dereference
                            (List.nth_exn arg_exps 1) tmp_gen
                        in
                        (String.concat ~sep:"\n" bindings) ^
                        "\n" ^
                        "//@ assert ether_addrp(" ^ (render_tterm expr) ^
                        ", ?" ^ (tmp_gen "dk") ^ ");\n" ^
                        (capture_a_chain "dh" params ^
                         capture_a_map "ether_addri" "dm" params ^
                         capture_a_vector "ether_addri" "dv" params);
                      | Ptr (Str ("StaticKey", _)) ->
                        (capture_a_map "stat_keyi" "stm" params)
                      | _ -> "#error unexpected key type")];
                 lemmas_after = [
                   reveal_the_other_mapp;
                   (fun {args;ret_name;arg_types;tmp_gen;_} ->
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
                         mvc_coherent_map_get_vec_half(" ^
                        (tmp_gen "dm") ^ ", " ^
                        (tmp_gen "dv") ^ ", " ^
                        (tmp_gen "dh") ^ ", " ^
                        (tmp_gen "dk") ^
                        ");\n\
                         } @*/"
                      | Ptr (Str ("StaticKey", _)) ->
                        "/*@ if (" ^ ret_name ^
                        " != 0) {\n\
                         assert static_keyp(" ^ (List.nth_exn args 1) ^
                        ", ?stkey);\n\
                         map_get_mem(" ^ (tmp_gen "stm") ^
                        ", stkey);\n\
                         forall_mem(pair(stkey, *" ^ (List.nth_exn args 2) ^
                        "), " ^ (tmp_gen "stm") ^
                        ", (st_entry_bound)(2));\n\
                         } @*/"
                      | _ -> "");];};
     "map_put", {ret_type = Static Void;
                 arg_types = [Static (Ptr map_struct);
                              Dynamic ["ether_addr", Ptr ether_addr_struct;
                                       "StaticKey", Ptr static_key_struct];
                              Static Sint32];
                 extra_ptr_types = [];
                 lemmas_before = [
                   (fun {tmp_gen;_} ->
                       "\n//@ assert mapp<ether_addri>(_, _, _, _, mapc(_, ?" ^ (tmp_gen "dm") ^
                       ", _));\n");
                   (fun {tmp_gen;_} ->
                      "\n/*@ {\n\
                       assert map_vec_chain_coherent<ether_addri>(" ^
                      (tmp_gen "dm") ^ ", ?" ^
                      (tmp_gen "dv") ^ ", ?" ^
                      (tmp_gen "dh") ^
                      ");\n\
                       mvc_coherent_dchain_non_out_of_space_map_nonfull<ether_addri>(" ^
                      (tmp_gen "dm") ^ ", " ^
                      (tmp_gen "dv") ^ ", " ^
                      (tmp_gen "dh") ^ ");\n} @*/");
                   hide_the_other_mapp];
                 lemmas_after = [
                   (fun {tmp_gen;args;_} ->
                      "\n/*@ {\n\
                       assert map_vec_chain_coherent<ether_addri>(" ^ (tmp_gen "dm") ^
                      ", ?" ^ (tmp_gen "dv") ^
                      ", ?" ^ (tmp_gen "dh") ^
                      ");\n\
                       ether_addri " ^ (tmp_gen "ea") ^ " = eaddrc(" ^ (List.nth_exn args 1) ^
                      "->a, " ^ (List.nth_exn args 1) ^
                      "->b, " ^ (List.nth_exn args 1) ^
                      "->c, " ^ (List.nth_exn args 1) ^
                      "->d, " ^ (List.nth_exn args 1) ^
                      "->e, " ^ (List.nth_exn args 1) ^
                      "->f);\n\
                       mvc_coherent_put<ether_addri>(" ^ (tmp_gen "dm") ^
                      ", " ^ (tmp_gen "dv") ^
                      ", " ^ (tmp_gen "dh") ^
                      ", " ^ (List.nth_exn args 2) ^
                      ", time_for_allocated_index, " ^ (tmp_gen "ea") ^ ");\n\
                       } @*/"
                   );
                   reveal_the_other_mapp];};
     "stub_core_trace_rx", {
                 ret_type = Static Void;
                 arg_types = stt [Ptr (Ptr rte_mbuf_struct);];
                 extra_ptr_types = estt ["incoming_package",
                                         rte_mbuf_struct;
                                         "user_buf_addr",
                                         stub_mbuf_content_struct];
                 lemmas_before = [];
                 lemmas_after = [(fun params -> "a_packet_received = true;\n" ^
                                       let arg0 = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0) in
                                       simplify_c_string (
                                         "received_on_port = " ^
                                         "(*" ^ arg0 ^ ")->port;\n" ^
                                         "received_packet_type = " ^
                                         "(*" ^ arg0 ^ ")->packet_type;\n") ^
                                         (copy_stub_mbuf_content "the_received_packet"
                                          ("*" ^ arg0)));
                                 ];};
     "stub_core_trace_tx", {
                 ret_type = Static Uint8;
                 arg_types = stt [Ptr rte_mbuf_struct; Uint16];
                 extra_ptr_types = estt ["user_buf_addr",
                                         stub_mbuf_content_struct];
                 lemmas_before = [
                     (fun params ->
                          let sent_pkt = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0) in
                            (copy_stub_mbuf_content "sent_packet"
                             (sent_pkt)) ^ "\n" ^
                            simplify_c_string (
                              "sent_on_port = " ^ (List.nth_exn params.args 1) ^ ";\n" ^
                              "sent_packet_type = (" ^
                              sent_pkt ^ ")->packet_type;"));];
                 lemmas_after = [(fun params -> "a_packet_sent = true;\n");];
                 };
     "stub_core_trace_free", {
                   ret_type = Static Void;
                   arg_types = stt [Ptr rte_mbuf_struct;];
                   extra_ptr_types = estt ["user_buf_addr",
                                           stub_mbuf_content_struct];
                   lemmas_before = [];
                   lemmas_after = [];};
     "flood", {ret_type = Static Ir.Sint32;
               arg_types = stt [Ptr rte_mbuf_struct; Ir.Uint16; Ir.Uint16];
               extra_ptr_types = estt ["user_buf_addr",
                                       stub_mbuf_content_struct];
               lemmas_before = [
               (fun params ->
                 let sent_pkt = Str.global_replace (Str.regexp_string "bis") "" (List.nth_exn params.args 0) in
                 (copy_stub_mbuf_content "sent_packet"
                    sent_pkt) ^ "\n" ^
                 "flooded_except_port = " ^
                 (List.nth_exn params.args 1) ^
                 ";\n" ^
                 "a_packet_flooded = true;\n" ^
                 "sent_packet_type = (" ^
                 sent_pkt ^ ")->packet_type;")];
               lemmas_after = [(fun _ -> "a_packet_sent = true;\n");];};
     "start_time", {ret_type = Static Sint64;
                    arg_types = [];
                    extra_ptr_types = [];
                    lemmas_before = [];
                    lemmas_after = [];};
     "vector_allocate", {ret_type = Static Sint32;
                         arg_types = stt [Sint32;
                                          Sint32;
                                          Fptr "vector_init_elem";
                                          Ptr (Ptr vector_struct)];
                         extra_ptr_types = [];
                         lemmas_before = [
                           tx_bl
                             "if (stat_vec_allocated) {\n\
                              if (dyn_keys_allocated) {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<uint16_t>(init_nothing_dv)\
                              (dyn_valp, sizeof(struct DynamicValue))(a) \
                              {\
                              call();\
                              }\n\
                              } else {\n\
                              produce_function_pointer_chunk \
                              vector_init_elem<ether_addri>(init_nothing_ea)\
                              (ether_addrp, sizeof(struct ether_addr))(a) \
                              {\
                              call();\
                              }\n
                              }\n\
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
                           (fun {tmp_gen;ret_name;_} ->
                              "/*@ if (" ^ ret_name ^
                              " && stat_vec_allocated && !dyn_keys_allocated) {\n\
                               assert mapp<ether_addri>(_, _, _, _, mapc(?" ^ (tmp_gen "cap") ^
                              ", ?" ^ (tmp_gen "map") ^
                              ", ?" ^ (tmp_gen "addr_map") ^
                              "));\n\
                               assert vectorp<ether_addri>(_, _, ?" ^ (tmp_gen "dks") ^
                              ", ?" ^ (tmp_gen "dkaddrs") ^
                              ");\n\
                               empty_kkeeper(" ^
                              (tmp_gen "dkaddrs") ^
                              ", " ^ (tmp_gen "dks") ^
                              ", " ^ (tmp_gen "addr_map") ^
                              ", " ^ (tmp_gen "cap") ^ ");\n } @*/");
                           (fun _ ->
                              "if (!stat_vec_allocated)\
                               stat_vec_allocated = true;\n\
                               else if (!dyn_keys_allocated)\ dyn_keys_allocated = true;");];};
     "vector_borrow_full", {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["StaticKey",
                                                  Ptr (Ptr static_key_struct);
                                                  "ether_addr",
                                                  Ptr (Ptr ether_addr_struct);
                                                  "DynamicValue",
                                                  Ptr (Ptr dynamic_value_struct)]];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["StaticKey",
                                                        static_key_struct;
                                                        "ether_addr",
                                                        ether_addr_struct;
                                                        "DynamicValue",
                                                        dynamic_value_struct]];
                            lemmas_before = [
                              (fun {arg_types;tmp_gen;args;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "StaticKey"->
                                   "/*@ {\n\
                                    if (!dyn_ks_borrowed) close hide_vector<ether_addri>(_, _, _, _);\n\
                                    if (!dyn_vs_borrowed) close hide_vector<uint16_t>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ether_addr"->
                                   "/*@ {\n\
                                    if (!stat_vec_borrowed) close hide_vector<stat_keyi>(_, _, _, _);\n\
                                    if (!dyn_vs_borrowed) close hide_vector<uint16_t>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    if (!dyn_ks_borrowed) close hide_vector<ether_addri>(_, _, _, _);\n\
                                    if (!stat_vec_borrowed) close hide_vector<stat_keyi>(_, _, _, _);\n\
                                    assert vectorp<uint16_t>(_, _, ?" ^ (tmp_gen "vec") ^
                                   ", _);\n\
                                    forall_mem(nth(" ^ (List.nth_exn args 1) ^ ", " ^
                                   (tmp_gen "vec") ^ "), " ^ (tmp_gen "vec") ^ ", snd);\n} @*/"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x))
                            ];
                            lemmas_after = [
                              (fun {arg_types;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "StaticKey"->
                                   "/*@ {\n\
                                    if (!dyn_ks_borrowed) open hide_vector<ether_addri>(_, _, _, _);\n\
                                    if (!dyn_vs_borrowed) open hide_vector<uint16_t>(_, _, _, _);\n} @*/\n\
                                    stat_vec_borrowed = true;"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ether_addr"->
                                   "/*@ {\n\
                                    if (!stat_vec_borrowed) open hide_vector<stat_keyi>(_, _, _, _);\n\
                                    if (!dyn_vs_borrowed) open hide_vector<uint16_t>(_, _, _, _);\n} @*/\n\
                                    dyn_ks_borrowed = true;"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    if (!dyn_ks_borrowed) open hide_vector<ether_addri>(_, _, _, _);\n\
                                    if (!stat_vec_borrowed) open hide_vector<stat_keyi>(_, _, _, _);\n} @*/\n\
                                    dyn_vs_borrowed = true;"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                              ];};
     "vector_borrow_half", {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["StaticKey",
                                                  Ptr (Ptr static_key_struct);
                                                  "ether_addr",
                                                  Ptr (Ptr ether_addr_struct)]];
                            extra_ptr_types = ["borrowed_cell",
                                               Dynamic ["StaticKey",
                                                        static_key_struct;
                                                        "ether_addr",
                                                        ether_addr_struct]];
                            lemmas_before = [
                              (fun {arg_types;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "StaticKey"->
                                   "/*@ {\n\
                                    close hide_vector<ether_addri>(_, _, _, _);\n\
                                    close hide_vector<uint16_t>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ether_addr"->
                                   "/*@ {\n\
                                    close hide_vector<stat_keyi>(_, _, _, _);\n\
                                    close hide_vector<uint16_t>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    close hide_vector<ether_addri>(_, _, _, _);\n\
                                    close hide_vector<stat_keyi>(_, _, _, _);\n} @*/"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x))
                            ];
                            lemmas_after = [
                              (fun {arg_types;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "StaticKey"->
                                   "/*@ {\n\
                                    open hide_vector<ether_addri>(_, _, _, _);\n\
                                    open hide_vector<uint16_t>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "ether_addr"->
                                   "/*@ {\n\
                                    open hide_vector<stat_keyi>(_, _, _, _);\n\
                                    open hide_vector<uint16_t>(_, _, _, _);\n} @*/"
                                 | Ptr (Ptr (Str (name, _)))
                                   when String.equal name "DynamicValue"->
                                   "/*@ {\n\
                                    open hide_vector<ether_addri>(_, _, _, _);\n\
                                    open hide_vector<stat_keyi>(_, _, _, _);\n} @*/"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                              ];};
     "vector_return_full", {ret_type = Static Void;
                            arg_types = [Static (Ptr vector_struct);
                                         Static Sint32;
                                         Dynamic ["StaticKey",
                                                  Ptr static_key_struct;
                                                  "ether_addr",
                                                  Ptr ether_addr_struct;
                                                  "DynamicValue",
                                                  Ptr dynamic_value_struct]];
                            extra_ptr_types = [];
                            lemmas_before = [
                              (fun {arg_types;tmp_gen;args;_} ->
                                 match List.nth_exn arg_types 2 with
                                 | Ptr (Str (name, _))
                                   when String.equal name "StaticKey"->
                                   "\n/*@ { \n\
                                    assert vector_accp<stat_keyi>(_, _, ?vectr, _, _, _); \n\
                                    update_id(" ^ (List.nth_exn args 1) ^
                                   ", vectr);\n\
                                    } @*/"
                                 | Ptr (Str (name, _))
                                   when String.equal name "ether_addr"->
                                   "\n/*@ { \n\
                                    assert vector_accp<ether_addri>(_, _, ?vectr, _, _, _); \n\
                                    update_id(" ^ (List.nth_exn args 1) ^
                                   ", vectr);\n\
                                      } @*/"
                                 | Ptr (Str (name, _))
                                   when String.equal name "DynamicValue"->
                                   "\n/*@ {\n\
                                    assert vector_accp<uint16_t>(_, _, ?" ^ (tmp_gen "vec") ^
                                   ", _, _, _);\n\
                                    forall_update<pair<uint16_t, bool> >(" ^ (tmp_gen "vec") ^
                                   ", snd, " ^ (List.nth_exn args 1) ^
                                   ", pair(" ^ (List.nth_exn args 2) ^ "->device, true));\n\
                                    update_id(" ^ (List.nth_exn args 1) ^
                                   ", " ^ (tmp_gen "vec") ^ ");\n\
                                   } @*/\n"
                                 | x -> "Error: unexpected argument type: " ^ (ttype_to_str x))
                              ];
                            lemmas_after = [];};
       "vector_return_half", {ret_type = Static Void;
                              arg_types = [Static (Ptr vector_struct);
                                           Static Sint32;
                                           Dynamic ["StaticKey",
                                                    Ptr static_key_struct;
                                                    "ether_addr",
                                                    Ptr ether_addr_struct]];
                              extra_ptr_types = [];
                              lemmas_before = [
                                (fun {args;tmp_gen;arg_types;_} ->
                                   match List.nth_exn arg_types 2 with
                                   | Ptr (Str (name, _)) ->
                                     if String.equal name "StaticKey" then
                                       "\n/*@ { \n\
                                        assert vector_accp<stat_keyi>(_, _, ?vectr, _, _, _); \n\
                                        update_id(" ^ (List.nth_exn args 1) ^
                                       ", vectr);\n\
                                        } @*/"
                                     else
                                       "\n/*@ { \n\
                                        assert vector_accp<ether_addri>(_, _, ?vectr, _, _, _); \n\
                                        update_id(" ^ (List.nth_exn args 1) ^
                                       ", vectr);\n\
                                        } @*/"
                                   | _ -> failwith "Wrong type for the last argument of vector_return");
                                (fun {arg_types;_} ->
                                   match List.nth_exn arg_types 2 with
                                   | Ptr (Str (name, _))
                                     when String.equal name "StaticKey" ->
                                     "/*@ {\n\
                                      if (dyn_ks_borrowed) close hide_vector_acc<ether_addri>(_, _, _, _, _, _);\n\
                                      if (dyn_vs_borrowed) close hide_vector_acc<uint16_t>(_, _, _, _, _, _);\n} @*/"
                                   | Ptr (Str (name, _))
                                     when String.equal name "ether_addr" ->
                                     "/*@ {\n\
                                      if (stat_vec_borrowed) close hide_vector_acc<stat_keyi>(_, _, _, _, _, _);\n\
                                      if (dyn_vs_borrowed) close hide_vector_acc<uint16_t>(_, _, _, _, _, _);\n} @*/"
                                   | Ptr (Str (name, _))
                                     when String.equal name "DynamicValue" ->
                                     "/*@ {\n\
                                      if (dyn_ks_borrowed) close hide_vector_acc<ether_addri>(_, _, _, _, _, _);\n\
                                      if (stat_vec_borrowed) close hide_vector_acc<stat_keyi>(_, _, _, _, _, _);\n} @*/"
                                   | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                              ];
                              lemmas_after = [
                                (fun {arg_types;_} ->
                                   match List.nth_exn arg_types 2 with
                                   | Ptr (Str (name, _))
                                     when String.equal name "StaticKey" ->
                                     "/*@ {\n\
                                      if (dyn_ks_borrowed) open hide_vector_acc<ether_addri>(_, _, _, _, _, _);\n\
                                      if (dyn_vs_borrowed) open hide_vector_acc<uint16_t>(_, _, _, _, _, _);\n} @*/\n\
                                      stat_vec_borrowed = false;"
                                   | Ptr (Str (name, _))
                                     when String.equal name "ether_addr" ->
                                     "/*@ {\n\
                                      if (stat_vec_borrowed) open hide_vector_acc<stat_keyi>(_, _, _, _, _, _);\n\
                                      if (dyn_vs_borrowed) open hide_vector_acc<uint16_t>(_, _, _, _, _, _);\n} @*/\n\
                                      dyn_ks_borrowed = false;"
                                   | Ptr (Str (name, _))
                                     when String.equal name "DynamicValue" ->
                                     "/*@ {\n\
                                      if (dyn_ks_borrowed) open hide_vector_acc<ether_addri>(_, _, _, _, _, _);\n\
                                      if (stat_vec_borrowed) open hide_vector_acc<stat_keyi>(_, _, _, _, _, _);\n} @*/\n\
                                      dyn_vs_borrowed = false;"
                                   | x -> "Error: unexpected argument type: " ^ (ttype_to_str x));
                              ];};]

let fixpoints =
  String.Map.of_alist_exn []

(* TODO: make external_ip symbolic *)
module Iface : Fspec_api.Spec =
struct
  let preamble = (In_channel.read_all "preamble.tmpl") ^
                 "void to_verify()\n\
                  /*@ requires true; @*/ \n\
                  /*@ ensures true; @*/\n{\n\
                  uint16_t received_on_port;\n\
                  uint32_t received_packet_type;\n\
                  struct stub_mbuf_content the_received_packet;\n\
                  int the_index_allocated = -1;\n\
                  int64_t time_for_allocated_index = 0;\n\
                  bool a_packet_received = false;\n\
                  struct stub_mbuf_content sent_packet;\n\
                  uint16_t sent_on_port;\n\
                  uint16_t flooded_except_port;\n\
                  bool a_packet_flooded = false;\n\
                  uint32_t sent_packet_type;\n\
                  bool a_packet_sent = false;\n"
                 ^ "//@ mapi<ether_addri> initial_dyn_map;\n"
                 ^ "//@ dchain initial_chain;\n"
                 ^ "//@ list<pair<uint16_t, bool> > initial_dyn_val_vec;\n"
                 ^ "//@ list<pair<ether_addri, bool> > initial_dyn_key_vec;\n"
                 ^ "//@ mapi<ether_addri> exprnd_dyn_map;\n"
                 ^ "//@ list<pair<uint16_t, bool> > exprnd_dyn_val_vec;\n"
                 ^ "//@ dchain exprnd_chain;\n"
                 ^
                 "/*@ //TODO: this hack should be \
                  converted to a system \n\
                  assume(sizeof(struct ether_addr) == 6);\n@*/\n\
                  /*@ assume(sizeof(struct DynamicValue) == 2);\n@*/\n\
                  /*@\
                  assume(sizeof(struct StaticKey) == 8);\n@*/\n"
                 ^
                 "/*@ assume(ether_addr_eq != static_key_eq); @*/\n"
                 ^
                 "bool stat_vec_allocated = false;\n"
                 ^
                 "bool dyn_keys_allocated = false;\n"
                 ^
                 "bool dyn_ks_borrowed = false;\n\
                  bool dyn_vs_borrowed = false;\n\
                  bool stat_vec_borrowed = false;\n"
  let fun_types = fun_types
  let fixpoints = fixpoints
  let boundary_fun = "bridge_loop_invariant_produce"
  let finishing_fun = "bridge_loop_invariant_consume"
  let eventproc_iteration_begin = "bridge_loop_invariant_produce"
  let eventproc_iteration_end = "bridge_loop_invariant_consume"
  let user_check_for_complete_iteration =
    In_channel.read_all "bridge_forwarding_property.tmpl"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

