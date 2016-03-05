open Core.Std

type c_type = | Ptr of c_type
              | Int
              | Uint32
              | Uint16
              | Uint8
              | Void
              | Str of string * (string * c_type) list
              | Ctm of string
              | Fptr of string

let rec c_type_to_str = function
  | Ptr c_type -> c_type_to_str c_type ^ "*"
  | Int -> "int" | Uint32 -> "uint32_t" | Uint16 -> "uint16_t"
  | Uint8 -> "uint8_t" | Void -> "void" | Str (name, _) -> "struct " ^ name
  | Ctm name -> name | Fptr name -> name ^ "*"

type lemma_term =
  | Txt of string
  | Rez_var

type lemma = lemma_term list

let is_void = function | Void -> true | _ -> false

let get_pointee = function | Ptr t -> t | _ -> failwith "not a plain pointer"

type fun_spec = {ret_type: c_type; arg_types: c_type list;
                 lemmas_before: string list; lemmas_after: lemma list;
                 leaks: string list;}

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
     "start_time", {ret_type = Void;
                    arg_types = [];
                    lemmas_before = [];
                    lemmas_after = [];
                    leaks = ["//@ leak last_time(_);"];};
     "dmap_allocate", {ret_type = Int;
                       arg_types =
                         [Int;Int;Ptr (Ctm "map_keys_equality");
                          Int;Int;Ptr (Ctm "map_keys_equality");
                          Int;Int;Ptr (Ptr dmap_struct)];
                       lemmas_before = [
                         "/*@ produce_function_pointer_chunk map_keys_equality<int_k>(int_key_eq)(int_k_p)(a, b) \
                          {\
                          call();\
                          }\
                          @*/";
                         "/*@ produce_function_pointer_chunk map_keys_equality<ext_k>(ext_key_eq)(ext_k_p)(a, b)\
                          {\
                          call();\
                          }\
                          @*/";
                         "\
  /*@ close exists<pair<pair<int_k, ext_k>, flw > >(pair(pair(ikc(0,0,0,0,0,0), ekc(0,0,0,0,0,0)),\
                                                         flwc(ikc(0,0,0,0,0,0),\
                                                              ekc(0,0,0,0,0,0),\
                                                              0,0,0,0,0,0,0,0,0)));\
    @*/\
 ";
                         "//@ close pred_arg2<void*, flw>(flw_p);";
                         "//@ close pred_arg4(nat_flow_p);"];
                       lemmas_after = [];
                       leaks = [];};
     "dmap_set_entry_condition", {ret_type = Void;
                                  arg_types = [Ptr (Ctm "entry_condition")];
                                  lemmas_before = [];
                                  lemmas_after = [];
                                  leaks = [];};
     "dchain_allocate", {ret_type = Int;
                         arg_types = [Int; Ptr (Ptr dchain_struct)];
                         lemmas_before = [];
                         lemmas_after = [];
                         leaks = [];};
     "loop_invariant_consume", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct)];
                                lemmas_before = [
                                  "//@ close dmap_dchain_coherent\
                                   (empty_dmap_fp(), empty_dchain_fp());";
                                  "//@ close evproc_loop_invariant(arg1, arg2);"];
                                lemmas_after = [];
                                leaks = [];};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct)];
                                lemmas_before = [];
                                lemmas_after = [
                                  [Txt "//@ open evproc_loop_invariant(?mp, ?chp);" ];
                                  [Txt "//@ assert dmap_dchain_coherent(?map,?chain);"]];
                                leaks = [
                                  "//@ leak last_time(_);";
                                  "//@ leak dmappingp<int_k, ext_k, flw>(_,_,_,_,_,_,_);";
                                  "//@ leak double_chainp(_,_,_);";
                                  "//@ leak dmap_dchain_coherent(_,_);"];};
     "loop_enumeration_begin", {ret_type = Void;
                                arg_types = [Int];
                                lemmas_before = [];
                                lemmas_after = [];
                                leaks = [];};
     "loop_enumeration_end", {ret_type = Void;
                              arg_types = [];
                              lemmas_before = [];
                              lemmas_after = [];
                              leaks = [];};
     "dmap_get_b", {ret_type = Int;
                    arg_types = [Ptr dmap_struct; Ptr ext_key_struct; Ptr Int;];
                    lemmas_before = [
                      "//@ close (ext_k_p(&arg3, ekc(user_buf0_36, user_buf0_34,\
                       user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      [Txt "//@ open (ext_k_p(_,_));" ];
                      [Txt "//@ if ("; Rez_var;
                       Txt "!=0)dmap_get_k2_gives_used(map, ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));" ];
                      [Txt "//@ if ("; Rez_var;
                       Txt "!=0)dmap_get_k2_limits(map, ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));" ];
                      [Txt "//@ if ("; Rez_var;
                       Txt "!=0) coherent_dmap_used_dchain_allocated\
                            (map, chain, \
                            dmap_get_k2_fp(map, ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));"];
                    ];
                    leaks = [];};
     "dmap_get_a", {ret_type = Int;
                    arg_types = [Ptr dmap_struct; Ptr int_key_struct; Ptr Int;];
                    lemmas_before = [
                      "//@ close (int_k_p(&arg3, ikc(user_buf0_34, user_buf0_36,\
                       user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      [Txt "//@ open (int_k_p(_,_));" ];
                      [Txt  "//@ if ("; Rez_var;
                       Txt ") dmap_get_k1_gives_used(map, ikc(user_buf0_34, user_buf0_36, \
                             user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));" ];
                      [Txt "//@ if ("; Rez_var;
                       Txt ") dmap_get_k1_limits(map, ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));" ];
                      [Txt "//@ if ("; Rez_var;
                       Txt "!=0) coherent_dmap_used_dchain_allocated\
                            (map, chain, \
                            dmap_get_k1_fp(map, ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));"];
                    ];
                    leaks = [];};
     "dmap_put", {ret_type = Int;
                  arg_types = [Ptr dmap_struct; Ptr flw_struct; Int;];
                  lemmas_before = [];
                  lemmas_after = [];
                  leaks = [];};
     "dmap_get_value", {ret_type = Void;
                        arg_types = [Ptr dmap_struct; Int; Ptr flw_struct;];
                        lemmas_before = [];
                        lemmas_after = [];
                        leaks = [
                          "//@ leak flw_p(_,_);";
                          "//@ leak nat_flow_p(_,_,_,_);"];};
     "expire_items", {ret_type = Int;
                      arg_types = [Ptr dchain_struct;
                                   Ptr dmap_struct;
                                   Uint32;];
                      lemmas_before = [];
                      lemmas_after = [];
                      leaks = [];};
     "dchain_allocate_new_index", {ret_type = Int;
                                   arg_types = [Ptr dchain_struct; Ptr Int; Uint32;];
                                   lemmas_before = [];
                                   lemmas_after = [];
                                   leaks = [];};
     "dchain_rejuvenate_index", {ret_type = Int;
                                 arg_types = [Ptr dchain_struct; Int; Uint32;];
                                 lemmas_before = [];
                                 lemmas_after = [];
                                 leaks = [];}
    ]
