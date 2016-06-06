open Core.Std
open Ir

type lemma = (string -> string list -> (string -> string) -> string)
type blemma = (string list -> (string -> string) -> string)
type leak_updater = (string -> string list ->
                     string String.Map.t -> string String.Map.t)

let tx_l str = (fun _ _ _ -> "/*@ " ^ str ^ " @*/" )
let tx_bl str = (fun _ _ -> "/*@ " ^ str ^ " @*/" )


let leak str ?(id=str) = (fun _ _ leaks ->
    String.Map.add leaks ~key:id ~data:("/*@ leak " ^ str ^ ";@*/"))

let on_rez_nz_leak str ?(id=str) = (fun rez_var _ leaks ->
    String.Map.add leaks ~key:id ~data:("/*@ if(" ^ rez_var ^
                                        "!=0) leak " ^ str ^ ";@*/"))

let remove_leak id = (fun _ _ leaks ->
    String.Map.remove leaks id)

let on_rez_nonzero str = (fun rez_var _ _ ->
    "/*@ if(" ^ rez_var ^ "!=0) " ^ str ^ "@*/")

let on_rez_nz f = (fun rez_var args tmp_gen ->
    "/*@ if(" ^ rez_var ^ "!=0) " ^ (f args tmp_gen) ^ " @*/")

type map_key = Int | Ext

let last_index_gotten = ref ""
let last_index_key = ref Int
let last_indexing_succ_ret_var = ref ""

let last_time_for_index_alloc = ref ""

let gen_get_fp map_name =
  match !last_index_key with
  | Int-> "dmap_get_k1_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"
  | Ext -> "dmap_get_k2_fp(" ^ map_name ^ ", " ^ !last_index_gotten ^ ")"

type fun_spec = {ret_type: ttype; arg_types: ttype list;
                 lemmas_before: blemma list; lemmas_after: lemma list;
                 leaks: leak_updater list;}

let dmap_struct = Str ( "DoubleMap", [] )
let dchain_struct = Str ( "DoubleChain", [] )
let ext_key_struct = Str ( "ext_key", ["ext_src_port", Uint16;
                                       "dst_port", Uint16;
                                       "ext_src_ip", Uint32;
                                       "dst_ip", Uint32;
                                       "ext_device_id", Uint8;
                                       "protocol", Uint8;] )
let int_key_struct = Str ( "int_key", ["int_src_port", Uint16;
                                       "dst_port", Uint16;
                                       "int_src_ip", Uint32;
                                       "dst_ip", Uint32;
                                       "int_device_id", Uint8;
                                       "protocol", Uint8;] )
let flw_struct = Str ("flow", ["ik", int_key_struct;
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
                       lemmas_after = [];
                       leaks = [
                         on_rez_nz_leak "dmappingp<int_k, ext_k, flw>\
                                         (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)"
                           ~id:"dmappingp";];};
     "dmap_set_entry_condition", {ret_type = Void;
                                  arg_types = [Ptr (Ctm "entry_condition")];
                                  lemmas_before = [];
                                  lemmas_after = [];
                                  leaks = [];};
     "dchain_allocate", {ret_type = Sint32;
                         arg_types = [Sint32; Ptr (Ptr dchain_struct)];
                         lemmas_before = [];
                         lemmas_after = [];
                         leaks = [
                           on_rez_nz_leak "double_chainp(_,_)"
                             ~id:"double_chainp";];};
     "loop_invariant_consume", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Uint32];
                                lemmas_before = [
                                  tx_bl "empty_dmap_dchain_coherent(1024);";
                                  tx_bl "index_range_of_empty(1024);";
                                  (fun args _ ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ ", " ^
                                     List.nth_exn args 2 ^"); @*/")];
                                lemmas_after = [];
                                leaks = [
                                  remove_leak "dmappingp";
                                  remove_leak "double_chainp";
                                  remove_leak "last_time";];};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct);
                                             Ptr Uint32];
                                lemmas_before = [];
                                lemmas_after = [
                                  tx_l "open evproc_loop_invariant(?mp, ?chp, ?t);";
                                  tx_l "assert dmap_dchain_coherent(?map,?chain);"];
                                leaks = [
                                  leak "last_time(_)" ~id:"last_time";
                                  leak "dmappingp<int_k, ext_k, flw>\
                                        (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)"
                                    ~id:"dmappingp";
                                  leak "double_chainp(_,_)"
                                    ~id:"double_chainp";
                                  leak "dmap_dchain_coherent(_,_)"];};
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
                      tx_bl "close (ext_k_p(&arg4, ekc(user_buf0_36, user_buf0_34,\
                             user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      tx_l "open (ext_k_p(_,_));";
                      on_rez_nz
                        (fun args _ ->
                           "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                           ");\n " ^
                           "dmap_get_k2_gives_used(cur_map, ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args _ ->
                           "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                           ");\n " ^
                           "dmap_get_k2_limits(cur_map, ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args _ ->
                        "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                         _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                        ");\n " ^
                        "dmap_get_k2_get_val(cur_map,ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args _ ->
                           "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                           ");\n " ^
                           "assert dmap_dchain_coherent(cur_map, ?cur_ch);\n" ^
                           "coherent_dmap_used_dchain_allocated\
                            (cur_map, cur_ch, \
                            dmap_get_k2_fp(cur_map, ekc(user_buf0_36, user_buf0_34, \
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
                      tx_bl "close (int_k_p(&arg4, ikc(user_buf0_34, user_buf0_36,\
                             user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      tx_l "open (int_k_p(_,_));";
                      on_rez_nz
                        (fun args _ ->
                           "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                           ");\n " ^
                           "dmap_get_k1_gives_used(cur_map, ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args _ ->
                           "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                           ");\n " ^
                           "dmap_get_k1_limits(cur_map, ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args _ ->
                        "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                         _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                        ");\n " ^
                        "dmap_get_k1_get_val(cur_map, ikc(user_buf0_34, user_buf0_36, \
                         user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));\n}");
                      on_rez_nz
                        (fun args _ ->
                           "{\n assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                           ");\n " ^
                           "assert dmap_dchain_coherent(cur_map, ?cur_ch);\n" ^
                           "coherent_dmap_used_dchain_allocated\
                            (cur_map, cur_ch, \
                            dmap_get_k1_fp(cur_map, ikc(user_buf0_34, user_buf0_36, \
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
                    (fun args _ -> "/*@{\n\
                                  assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                                  _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                                 ");\n\
                                  assert dmap_dchain_coherent(cur_map, ?cur_ch);\n\
                                  ext_k ek = ekc(tmp1, user_buf0_36,\
                                  184789184, user_buf0_30, 1, user_buf0_23);\n\
                                  if (dmap_has_k2_fp(cur_map, ek)) {\n\
                                  int index = dmap_get_k2_fp(cur_map, ek);\n\
                                  dmap_get_k2_gives_used(cur_map, ek);\n\
                                  flw value = dmap_get_val_fp(cur_map, index);\n\
                                  dmap_get_by_index_rp(cur_map, index);\n\
                                  dmap_get_by_k2_invertible(cur_map, ek);\n\
                                  assert(index == new_index_0);\n\
                                  assert(true == dmap_index_used_fp(cur_map, new_index_0));\n\
                                  coherent_dmap_used_dchain_allocated(cur_map,\
                                  cur_ch, new_index_0);\n\
                                  assert(true == dchain_allocated_index_fp(cur_map, new_index_0));\n\
                                  assert(false);\n\
                                  }\n\
                                  }@*/");
                    (fun args _ ->
                    "/*@{\n\
                     assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                     _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                    ");\n\
                     assert dmap_dchain_coherent(cur_map, ?cur_ch);\n\
                     if (dmap_index_used_fp(cur_map, new_index_0)) {\n\
                     coherent_dmap_used_dchain_allocated(cur_map, cur_ch, new_index_0);\n\
                     }\n\
                     }@*/");
                    (fun args _ ->
                       "//@assert dmappingp<int_k,ext_k,flw>(?map_before_put,\
                        _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^ ");\n");
                    tx_bl "{\n\
                           assert dmap_dchain_coherent(map_before_put, ?ch);\n\
                           coherent_dchain_non_out_of_space_map_nonfull\
                           (map_before_put, ch);\n\
                           }";];
                  lemmas_after = [
                    tx_l "open flw_p(_,_);";
                    tx_l "open int_k_p(_,_);";
                    tx_l "open ext_k_p(_,_);";
                    (fun ret_var _ _ ->
                       "/*@if (" ^ ret_var ^
                       "!= 0) {\n\
                        dmap_put_get(map_before_put,\
                        flwc(ikc(user_buf0_34, user_buf0_36,\
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                        ekc(tmp1, user_buf0_36, 184789184, user_buf0_30,\
                        1, user_buf0_23),\n\
                        user_buf0_34, tmp1, user_buf0_36, user_buf0_26,\n\
                        184789184, user_buf0_30, cmplx1, 1, user_buf0_23),\n\
                        ikc(user_buf0_34, user_buf0_36, user_buf0_26,\
                        user_buf0_30, cmplx1, user_buf0_23),\n\
                        ekc(tmp1, user_buf0_36, 184789184,\
                        user_buf0_30, 1, user_buf0_23),\n\
                        new_index_0);\n\
                        }@*/"
                    );
                    (fun ret_var _ _ ->
                       "/*@if (" ^ ret_var ^
                       "!= 0) {\n\
                       assert dmap_dchain_coherent(map_before_put, ?cur_ch);\n\
                       coherent_put_allocated_preserves_coherent\n\
                       (map_before_put, cur_ch,\
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
                        new_index_0, " ^ !last_time_for_index_alloc ^ ");\
                        }@*/");
                  ]
                  ;
                  leaks = [];};
     "dmap_get_value", {ret_type = Void;
                        arg_types = [Ptr dmap_struct; Sint32; Ptr flw_struct;];
                        lemmas_before = [];
                        lemmas_after = [
                          (fun _ args _ ->
                             "/*@{ " ^
                             "assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                              _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 0) ^
                             ");\n\
                              if (" ^ !last_indexing_succ_ret_var ^ "!= 0) { \n\
                              assert dmap_dchain_coherent(cur_map, ?cur_ch);\n\
                              coherent_dmap_used_dchain_allocated(cur_map, cur_ch," ^
                             (gen_get_fp "cur_map") ^
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
                        (fun args _ ->
                           if String.equal !last_index_gotten "" then ""
                           else
                           "/*@ {\n" ^
                           "assert dmappingp<int_k,ext_k,flw>(?cur_map,\
                            _,_,_,_,_,_,_,_,_,_,_,_,_," ^ (List.nth_exn args 1) ^ ");\n" ^
                           "assert dmap_dchain_coherent(cur_map, ?cur_chain);\n\
                            dmap_erase_all_has_trans(cur_map, ikc(user_buf0_34,\
                            user_buf0_36, user_buf0_26, user_buf0_30, cmplx1, user_buf0_23),\n\
                            dchain_get_expired_indexes_fp(cur_chain, " ^ (List.nth_exn args 2) ^
                           "));\n\
                            }@*/");
                        (fun args _ ->
                           "/*@ {\n\
                            assert double_chainp(?cur_chain, " ^
                           (List.nth_exn args 0) ^
                           ");\n\
                            expire_preserves_index_range(cur_chain," ^
                           (List.nth_exn args 2) ^ ");\n
                           length_nonnegative(\
                            dchain_get_expired_indexes_fp(cur_chain, " ^
                           (List.nth_exn args 2) ^ "));\n\
                            if (length(dchain_get_expired_indexes_fp(cur_chain, " ^
                           (List.nth_exn args 2) ^
                           ")) > 0 ) {\n\
                            expire_old_dchain_nonfull\
                            (" ^ (List.nth_exn args 0) ^ ", cur_chain, " ^
                           (List.nth_exn args 2) ^
                           ");\n\
                            }} @*/");
                        ];
                      lemmas_after = [
                        (fun _ args _ ->
                           "/*@ {\n" ^
                           "assert dmap_dchain_coherent(?mmmmap, ?ccchhhh);\n\
                            expire_preserves_coherent(mmmmap, ccchhhh, " ^
                           (List.nth_exn args 2) ^ ");\n}@*/");
                      ];
                      leaks = [];};
     "dchain_allocate_new_index", {ret_type = Sint32;
                                   arg_types = [Ptr dchain_struct; Ptr Sint32; Uint32;];
                                   lemmas_before = [
                                     (fun args tmp ->
                                        "//@ assert double_chainp(\
                                         ?" ^ (tmp "chain_before_alloc") ^ ", " ^
                                        (List.nth_exn args 0) ^
                                        ");\n ");];
                                   lemmas_after = [
                                     on_rez_nz
                                       (fun args tmp ->
                                          "{\n allocate_preserves_index_range(" ^
                                          (tmp "chain_before_alloc") ^
                                          ", *" ^
                                          (List.nth_exn args 1) ^
                                          ", " ^ (List.nth_exn args 2) ^ ");\n}");
                                     (fun _ args _ ->
                                        last_time_for_index_alloc :=
                                          (List.nth_exn args 2);
                                        "")
                                   ];
                                   leaks = [];};
     "dchain_rejuvenate_index", {ret_type = Sint32;
                                 arg_types = [Ptr dchain_struct; Sint32; Uint32;];
                                 lemmas_before = [];
                                 lemmas_after = [
                                   (fun reg_var args _ ->
                                      "/*@ if (" ^ reg_var ^ " != 0) {\n" ^
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
    "nat_int_fp", {v=Bop(And,
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
