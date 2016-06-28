
open Core.Std
open Fspec_api

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""

let last_time_for_index_alloc = ref ""

let gen_get_fp map_name =
  match !last_index_key with
  | Int-> "dmap_get_k1_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"
  | Ext -> "dmap_get_k2_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"

let capture_map map_name ptr_num args tmp =
  "//@ assert dmappingp<int_k,ext_k,flw>(?" ^ (tmp map_name) ^
  ",_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args ptr_num) ^ ");\n"

let capture_map_ex map_name vk1 vk2 ptr_num args tmp =
  "//@ assert dmappingp<int_k,ext_k,flw>(?" ^ (tmp map_name) ^
  ",_,_,_,_,_,_,_,_,?" ^ (tmp vk1) ^ ",?" ^ (tmp vk2) ^
  ",_,_," ^
  (List.nth_exn args ptr_num) ^ ");\n"

let capture_chain ch_name ptr_num args tmp =
  "//@ assert double_chainp(?" ^ (tmp ch_name) ^ ", " ^
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

let fun_types =
  String.Map.of_alist_exn
    ["current_time", {ret_type = Uint32;
                      arg_types = [];
                      lemmas_before = [];
                      lemmas_after = [];
                      leaks = [];};
     "start_time", {ret_type = Uint32;
                    arg_types = [];
                    lemmas_before = [];
                    lemmas_after = [];
                    leaks = [leak "last_time(_)" ~id:"last_time"];};
     "dmap_allocate", {ret_type = Sint32;
                       arg_types =
                         [Ptr (Ctm "map_keys_equality"); Ptr (Ctm "map_key_hash");
                          Ptr (Ctm "map_keys_equality"); Ptr (Ctm "map_key_hash");
                          Sint32; Ptr (Ctm "uq_value_copy");
                          Ptr (Ctm "uq_value_destr");
                          Ptr (Ctm "dmap_extract_keys"); Ptr (Ctm "dmap_pack_keys");
                          Sint32;
                          Ptr (Ptr dmap_struct)];
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
                         (fun args _ ->
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
                         tx_bl "close dmap_record_property2(nat_ext_fp);"];
                       lemmas_after = [
                         tx_l "empty_dmap_cap\
                               <int_k,ext_k,flw>(1024);";];
                       leaks = [
                         on_rez_nz_leak "dmappingp<int_k, ext_k, flw>\
                                         (_,_,_,_,_,_,_,_,_,_,_,_,_,_)"
                           ~id:"dmappingp";];};
     "dmap_set_entry_condition", {ret_type = Void;
                                  arg_types = [Ptr (Ctm "entry_condition")];
                                  lemmas_before = [];
                                  lemmas_after = [];
                                  leaks = [];};
     "dchain_allocate", {ret_type = Sint32;
                         arg_types = [Sint32; Ptr (Ptr dchain_struct)];
                         lemmas_before = [];
                         lemmas_after = [
                           on_rez_nz (fun _ _ ->
                               "empty_dmap_dchain_coherent\
                                <int_k,ext_k,flw>(1024);");
                           tx_l "index_range_of_empty(1024, 0);";];
                         leaks = [
                           on_rez_nz_leak "double_chainp(_,_)"
                             ~id:"double_chainp";
                           on_rez_nz_leak "dmap_dchain_coherent(_,_)"
                             ~id:"dmap_dchain_coherent";
                         ];};
     "loop_invariant_consume", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Uint32];
                                lemmas_before = [
                                  (fun args _ ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ ", " ^
                                     List.nth_exn args 2 ^"); @*/")];
                                lemmas_after = [];
                                leaks = [
                                  remove_leak "dmappingp";
                                  remove_leak "double_chainp";
                                  remove_leak "last_time";
                                  remove_leak "dmap_dchain_coherent"];};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Ptr Uint32];
                                lemmas_before = [];
                                lemmas_after = [
                                  tx_l "open evproc_loop_invariant(?mp, ?chp, ?t);";
                                  tx_l "assert dmap_dchain_coherent(?map,?chain);";
                                  tx_l "coherent_same_cap(map, chain);";];
                                leaks = [
                                  leak "last_time(_)" ~id:"last_time";
                                  leak "dmappingp<int_k, ext_k, flw>\
                                        (_,_,_,_,_,_,_,_,_,_,_,_,_,_)"
                                    ~id:"dmappingp";
                                  leak "double_chainp(_,_)"
                                    ~id:"double_chainp";
                                  leak "dmap_dchain_coherent(_,_)"
                                    ~id:"dmap_dchain_coherent"];};
     "loop_enumeration_begin", {ret_type = Void;
                                arg_types = [Sint32];
                                lemmas_before = [];
                                lemmas_after = [];
                                leaks = [];};
     "loop_enumeration_end", {ret_type = Void;
                              arg_types = [];
                              lemmas_before = [];
                              lemmas_after = [];
                              leaks = [];};
     "dmap_get_b", {ret_type = Sint32;
                    arg_types = [Ptr dmap_struct; Ptr ext_key_struct; Ptr Sint32;];
                    lemmas_before = [
                      capture_map "cur_map" 0;
                      tx_bl "close (ext_k_p(&arg4, ekc(user_buf0_36, user_buf0_34,\
                             user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      tx_l "open (ext_k_p(_,_));";
                      on_rez_nz
                        (fun args tmp ->
                           "{\n dmap_get_k2_limits(" ^
                           (tmp "cur_map") ^
                           ", ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args tmp ->
                           "{\n dmap_get_k2_get_val(" ^
                           (tmp "cur_map") ^
                           ",ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args tmp ->
                           "{\n assert dmap_dchain_coherent(" ^
                           (tmp "cur_map") ^
                           ", ?cur_ch);\n\
                            coherent_dmap_used_dchain_allocated(" ^
                           (tmp "cur_map") ^ ", cur_ch, dmap_get_k2_fp(" ^
                           (tmp "cur_map") ^ ", ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));\n}");
                      (fun ret_var _ _ ->
                         last_index_gotten :=
                           "ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)";
                         last_index_key := Ext;
                         last_indexing_succ_ret_var := ret_var;
                         "");
                    ];
                    leaks = [];};
     "dmap_get_a", {ret_type = Sint32;
                    arg_types = [Ptr dmap_struct; Ptr int_key_struct; Ptr Sint32;];
                    lemmas_before = [
                      capture_map "cur_map" 0;
                      tx_bl "close (int_k_p(&arg4, ikc(user_buf0_34, user_buf0_36,\
                             user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      tx_l "open (int_k_p(_,_));";
                      on_rez_nz
                        (fun args tmp ->
                           "{\n dmap_get_k1_limits(" ^
                           (tmp "cur_map") ^
                           ", ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args tmp ->
                           "{\n dmap_get_k1_get_val(" ^
                           (tmp "cur_map") ^
                           ", ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args tmp ->
                           "{\n assert dmap_dchain_coherent(" ^
                           (tmp "cur_map") ^ ", ?cur_ch);\n" ^
                           "coherent_dmap_used_dchain_allocated(" ^
                           (tmp "cur_map") ^
                           ", cur_ch, dmap_get_k1_fp(" ^
                           (tmp "cur_map") ^
                           ", ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));\n}");
                      (fun ret_var _ _ ->
                         last_index_gotten :=
                           "ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)";
                         last_index_key := Int;
                         last_indexing_succ_ret_var := ret_var;
                         "");
                    ];
                    leaks = [];};
     "dmap_put", {ret_type = Sint32;
                  arg_types = [Ptr dmap_struct; Ptr flw_struct; Sint32;];
                  lemmas_before = [
                    capture_map_ex "cur_map" "vk1" "vk2" 0;
                    (fun args _ -> "/*@ close int_k_p(" ^ (List.nth_exn args 1) ^
                    ".ik, ikc(user_buf0_34, user_buf0_36, user_buf0_26,\
                     user_buf0_30, cmplx1, user_buf0_23));@*/");
                    (fun args _ -> "/*@ close ext_k_p(" ^ (List.nth_exn args 1) ^
                    ".ek, ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                     1, user_buf0_23));@*/");
                    (fun args _ -> "/*@ close flw_p(" ^ (List.nth_exn args 1) ^
                    ", flwc(ikc(user_buf0_34, user_buf0_36, user_buf0_26, user_buf0_30,\
                     cmplx1, user_buf0_23), ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                     1, user_buf0_23), user_buf0_34, tmp1, user_buf0_36, user_buf0_26,\
                     184789184, user_buf0_30, cmplx1, 1, user_buf0_23));@*/");
                    (fun args tmp ->
                       "/*@{\n\
                        assert dmap_dchain_coherent(" ^
                         (tmp "cur_map") ^
                       ", ?cur_ch);\n\
                        ext_k ek = ekc(tmp1, user_buf0_36,\
                        184789184, user_buf0_30, 1, user_buf0_23);\n\
                        if (dmap_has_k2_fp(" ^ (tmp "cur_map") ^
                       ", ek)) {\n\
                        int index = dmap_get_k2_fp(" ^ (tmp "cur_map") ^
                       ", ek);\n\
                        dmap_get_k2_limits(" ^ (tmp "cur_map") ^
                       ", ek);\n\
                        flw value = dmap_get_val_fp(" ^ (tmp "cur_map") ^
                       ", index);\n\
                        dmap_get_by_index_rp(" ^ (tmp "cur_map") ^
                       ", index);\n\
                        dmap_get_by_k2_invertible(" ^ (tmp "cur_map") ^
                       ", ek);\n\
                        assert(index == new_index_0);\n\
                        assert(true == dmap_index_used_fp(" ^ (tmp "cur_map") ^
                       ", new_index_0));\n\
                        coherent_dmap_used_dchain_allocated(" ^ (tmp "cur_map") ^
                       ", cur_ch, new_index_0);\n\
                        assert(true == dchain_allocated_index_fp(" ^
                       (tmp "cur_map") ^
                       ", new_index_0));\n\
                        assert(false);\n\
                        }\n\
                        }@*/");
                    (fun args tmp ->
                       "/*@{\n\
                        assert dmap_dchain_coherent(" ^ (tmp "cur_map") ^
                       ", ?cur_ch);\n\
                        if (dmap_index_used_fp(" ^ (tmp "cur_map") ^
                       ", new_index_0)) {\n\
                        coherent_dmap_used_dchain_allocated(" ^ (tmp "cur_map") ^
                       ", cur_ch, new_index_0);\n\
                        }\n\
                        }@*/");
                    (fun args tmp ->
                       "/*@ dmap_put_preserves_cap(" ^ (tmp "cur_map") ^
                       ", new_index_0, flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                        ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, tmp1, user_buf0_36, user_buf0_26,\n\
                        184789184, user_buf0_30, cmplx1, 1, user_buf0_23)," ^
                       (tmp "vk1") ^ ", " ^ (tmp "vk2") ^ "); @*/");
                    (fun args tmp ->
                      "/*@ {\n\
                       assert dmap_dchain_coherent(" ^ (tmp "cur_map") ^
                      ", ?ch);\n\
                       coherent_dchain_non_out_of_space_map_nonfull(" ^
                      (tmp "cur_map") ^ ", ch);\n} @*/");];
                  lemmas_after = [
                    tx_l "open flw_p(_,_);";
                    tx_l "open int_k_p(_,_);";
                    tx_l "open ext_k_p(_,_);";
                    (fun ret_var _ tmp ->
                       "/*@if (" ^ ret_var ^
                       "!= 0) {\n\
                        dmap_put_get(" ^
                       (tmp "cur_map") ^
                       ",new_index_0,\
                        flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                        ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, tmp1, user_buf0_36, user_buf0_26,\n\
                        184789184, user_buf0_30, cmplx1, 1, user_buf0_23),\n" ^
                       (tmp "vk1") ^ ", " ^
                       (tmp "vk2") ^ ");\n}@*/");
                    (fun ret_var _ tmp ->
                       "/*@if (" ^ ret_var ^
                       "!= 0) {\n\
                        assert dmap_dchain_coherent(" ^
                       (tmp "cur_map") ^
                       ", ?cur_ch);\n\
                        coherent_put_allocated_preserves_coherent\n(" ^
                       (tmp "cur_map") ^
                       ", cur_ch,\
                        ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                        ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                        1, user_buf0_23),\
                        flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                        ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, tmp1, user_buf0_36, user_buf0_26,\n\
                        184789184, user_buf0_30, cmplx1, 1, user_buf0_23),\
                        new_index_0, " ^ !last_time_for_index_alloc ^
                       ", " ^ (tmp "vk1") ^ ", " ^ (tmp "vk2") ^ ");\
                        }@*/");
                  ]
                  ;
                  leaks = [];};
     "dmap_get_value", {ret_type = Void;
                        arg_types = [Ptr dmap_struct; Sint32; Ptr flw_struct;];
                        lemmas_before = [
                          capture_map "cur_map" 0;
                          (fun args tmp ->
                             "/*@ {\
                              assert dmap_dchain_coherent(" ^ (tmp "cur_map") ^
                             ", ?cur_ch);\n\
                              coherent_same_cap(" ^ (tmp "cur_map") ^
                             ", cur_ch);\n\
                              }@*/");
                          (fun args _ ->
                             "//@ flow_to_chars(" ^
                             (List.nth_exn args 2) ^ ");")];
                        lemmas_after = [
                          (fun _ args tmp ->
                             "/*@{ if (" ^ !last_indexing_succ_ret_var ^
                             "!= 0) { \n\
                              assert dmap_dchain_coherent(" ^ (tmp "cur_map") ^
                             ", ?cur_ch);\n\
                              coherent_dmap_used_dchain_allocated(" ^
                             (tmp "cur_map") ^ ", cur_ch," ^
                             (gen_get_fp (tmp "cur_map")) ^
                             ");\n\
                              }}@*/");
                          tx_l "assert(0 <= cmplx1 && cmplx1 < RTE_NUM_DEVICES);";
                          (fun _ args _ ->
                             "/*@\
                              open flw_p(" ^ (List.nth_exn args 2) ^
                             ", _);\n\
                              @*/");
                          tx_l "open int_k_p(_,_);";
                          tx_l "open ext_k_p(_,_);";
                        ];
                        leaks = [];};
     "expire_items", {ret_type = Sint32;
                      arg_types = [Ptr dchain_struct;
                                   Ptr dmap_struct;
                                   Uint32;];
                      lemmas_before = [
                        capture_chain "cur_ch" 0;
                        capture_map_ex "cur_map" "vk1" "vk2" 1;
                        (fun args tmp ->
                           if String.equal !last_index_gotten "" then ""
                           else
                           "/*@ { \n\
                            dmap_erase_all_has_trans(" ^
                           (tmp "cur_map") ^
                           ", ikc(user_buf0_34,\
                            user_buf0_36, user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                            dchain_get_expired_indexes_fp(" ^
                           (tmp "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           "), " ^ (tmp "vk1") ^ ", " ^ (tmp "vk2") ^
                           ");\n\
                            coherent_same_cap(" ^
                           (tmp "cur_map") ^ ", " ^ (tmp "cur_ch") ^
                           ");\n } @*/");
                        (fun args tmp ->
                           "/*@ {\n\
                            expire_preserves_index_range(" ^
                           (tmp "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ");\n
                           length_nonnegative(\
                            dchain_get_expired_indexes_fp(" ^
                           (tmp "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           "));\n\
                            if (length(dchain_get_expired_indexes_fp(" ^
                           (tmp "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ")) > 0 ) {\n\
                            expire_old_dchain_nonfull\
                            (" ^ (List.nth_exn args 0) ^ ", " ^
                           (tmp "cur_ch") ^ ", " ^
                           (List.nth_exn args 2) ^
                           ");\n\
                            }} @*/");
                        (fun args tmp ->
                           "/*@ dmap_erase_all_preserves_cap(" ^
                           (tmp "cur_map") ^ ", " ^
                           "dchain_get_expired_indexes_fp(" ^
                           (tmp "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^
                           "), " ^ (tmp "vk1") ^ ", " ^
                           (tmp "vk2") ^ "); @*/");
                        (fun _ tmp ->
                           "/*@ coherent_same_cap(" ^
                           (tmp "cur_map") ^ ", " ^ (tmp "cur_ch") ^ ");@*/\n");
                        (fun args tmp ->
                           "//@ expire_olds_keeps_high_bounded(" ^
                           (tmp "cur_ch") ^
                           ", " ^ (List.nth_exn args 2) ^
                           ");\n");
                        ];
                      lemmas_after = [
                      ];
                      leaks = [];};
     "dchain_allocate_new_index", {ret_type = Sint32;
                                   arg_types = [Ptr dchain_struct; Ptr Sint32; Uint32;];
                                   lemmas_before = [
                                     capture_chain "cur_ch" 0;
                                   ];
                                   lemmas_after = [
                                     on_rez_nz
                                       (fun args tmp ->
                                          "{\n allocate_preserves_index_range(" ^
                                          (tmp "cur_ch") ^
                                          ", *" ^
                                          (List.nth_exn args 1) ^
                                          ", " ^ (List.nth_exn args 2) ^ ");\n}");
                                     (fun _ args tmp ->
                                        "//@ allocate_keeps_high_bounded(" ^
                                        (tmp "cur_ch") ^
                                        ", *" ^ (List.nth_exn args 1) ^
                                        ", " ^ (List.nth_exn args 2) ^
                                        ");\n");
                                     (fun _ args _ ->
                                        last_time_for_index_alloc :=
                                          (List.nth_exn args 2);
                                        "");
                                   ];
                                   leaks = [];};
     "dchain_rejuvenate_index", {ret_type = Sint32;
                                 arg_types = [Ptr dchain_struct; Sint32; Uint32;];
                                 lemmas_before = [
                                   capture_chain "cur_ch" 0;
                                   (fun args tmp ->
                                      "/*@ {\n\
                                       assert dmap_dchain_coherent(?cur_map, " ^
                                      (tmp "cur_ch") ^
                                      ");\n coherent_same_cap(cur_map, " ^
                                      (tmp "cur_ch") ^
                                      ");} @*/");
                                   (fun args tmp ->
                                      "//@ rejuvenate_keeps_high_bounded(" ^
                                      (tmp "cur_ch") ^
                                      ", " ^ (List.nth_exn args 1) ^
                                      ", " ^ (List.nth_exn args 2) ^
                                      ");\n");];
                                 lemmas_after = [
                                   (fun ret_var args _ ->
                                      "/*@ if (" ^ ret_var ^ " != 0) { \n" ^
                                      "assert dmap_dchain_coherent(?cur_map,?ch);\n" ^
                                      "rejuvenate_preserves_coherent(cur_map, ch, " ^
                                      (List.nth_exn args 1) ^ ", " ^ (List.nth_exn args 2) ^
                                      ");\n\
                                       rejuvenate_preserves_index_range(ch," ^
                                      (List.nth_exn args 1) ^ ", " ^ (List.nth_exn args 2) ^
                                      ");\n}@*/");];
                                 leaks = [];}
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
                                       {v=Str_idx({v=Id "Arg0";t=Unknown},"edid");t=Unknown});
                                 t=Unknown},
                                {v=Bop(Lt,
                                       {v=Str_idx({v=Id "Arg0";t=Unknown},"edid");t=Unknown},
                                       {v=Int 2;t=Sint32});t=Unknown});
                          t=Boolean},
                         {v=Bop(Eq,
                                {v=Str_idx({v=Id "Arg0";t=Unknown},"edid");t=Unknown},
                                {v=Bop(Add,
                                       {v=Int 2747;t=Sint32},
                                       {v=Id "Arg1";t=Unknown});t=Unknown});
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

module Iface : Fspec_api.Spec =
struct
  let preamble = In_channel.read_all "preamble.tmpl"
  let fun_types = fun_types
  let fixpoints = fixpoints
  let boundary_fun = "loop_invariant_consume"
end

(* Register the module *)
let () =
  Fspec_api.spec := Some (module Iface) ;

