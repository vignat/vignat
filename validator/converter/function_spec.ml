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
              | Bool
              | Sunknown
              | Uunknown
              | Unknown

let rec c_type_to_str = function
  | Ptr c_type -> c_type_to_str c_type ^ "*"
  | Int -> "int" | Uint32 -> "uint32_t" | Uint16 -> "uint16_t"
  | Uint8 -> "uint8_t" | Void -> "void" | Str (name, _) -> "struct " ^ name
  | Ctm name -> name | Fptr name -> name ^ "*" | Bool -> "bool" | Unknown -> "???"
  | Sunknown -> "s??" | Uunknown -> "u??"

type lemma = (string -> string list -> string)
type blemma = (string list -> string)

let tx_l str = (fun _ _ -> "/*@"^str^"@*/" )
let tx_bl str = (fun _ -> "/*@"^str^"@*/" )

let on_rez_nonzero str = (fun rez_var _ ->
    "/*@ if(" ^ rez_var ^ "==1) " ^ str ^ "@*/")

let last_index_gotten = ref ""

let is_void = function | Void -> true | _ -> false

let get_pointee = function | Ptr t -> t | _ -> failwith "not a plain pointer"

type fun_spec = {ret_type: c_type; arg_types: c_type list;
                 lemmas_before: blemma list; lemmas_after: lemma list;
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
                         tx_bl "produce_function_pointer_chunk \
                                map_keys_equality<int_k>(int_key_eq)(int_k_p)(a, b) \
                                {\
                                call();\
                                }";
                         tx_bl "produce_function_pointer_chunk \
                                map_keys_equality<ext_k>(ext_key_eq)(ext_k_p)(a, b)\
                                {\
                                call();\
                                }";
                         tx_bl "close exists<pair<pair<int_k, ext_k>, flw > >\
                                (pair(pair(ikc(0,0,0,0,0,0), ekc(0,0,0,0,0,0)),\
                                      flwc(ikc(0,0,0,0,0,0),\
                                           ekc(0,0,0,0,0,0),\
                                           0,0,0,0,0,0,0,0,0)));";
                         tx_bl "close pred_arg2<void*, flw>(flw_p);";
                         tx_bl "close pred_arg4(nat_flow_p);"];
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
                                  tx_bl "close dmap_dchain_coherent\
                                         (empty_dmap_fp(), empty_dchain_fp());";
                                  (fun args ->
                                     "/*@ close evproc_loop_invariant(*" ^
                                     List.nth_exn args 0 ^ ", *" ^
                                     List.nth_exn args 1 ^ "); @*/")];
                                lemmas_after = [];
                                leaks = [];};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = [Ptr (Ptr dmap_struct);
                                             Ptr (Ptr dchain_struct)];
                                lemmas_before = [];
                                lemmas_after = [
                                  tx_l "open evproc_loop_invariant(?mp, ?chp);";
                                  tx_l "assert dmap_dchain_coherent(?map,?chain);"];
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
                      tx_bl "close (ext_k_p(&arg3, ekc(user_buf0_36, user_buf0_34,\
                             user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      tx_l "open (ext_k_p(_,_));";
                      on_rez_nonzero
                        "dmap_get_k2_gives_used(map, ekc(user_buf0_36, user_buf0_34, \
                         user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));";
                      on_rez_nonzero
                        "dmap_get_k2_limits(map, ekc(user_buf0_36, user_buf0_34, \
                         user_buf0_30, user_buf0_26, cmplx1, user_buf0_23));";
                      on_rez_nonzero
                       "coherent_dmap_used_dchain_allocated\
                        (map, chain, \
                        dmap_get_k2_fp(map, ekc(user_buf0_36, user_buf0_34, \
                        user_buf0_30, user_buf0_26, cmplx1, user_buf0_23)));";
                      (fun _ _ ->
                         last_index_gotten :=
                           "dmap_get_k2_fp(map, " ^
                           "ekc(user_buf0_36, user_buf0_34, \
                            user_buf0_30, user_buf0_26, cmplx1, user_buf0_23))";
                         "");
                    ];
                    leaks = [];};
     "dmap_get_a", {ret_type = Int;
                    arg_types = [Ptr dmap_struct; Ptr int_key_struct; Ptr Int;];
                    lemmas_before = [
                      tx_bl "close (int_k_p(&arg3, ikc(user_buf0_34, user_buf0_36,\
                             user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));"];
                    lemmas_after = [
                      tx_l "open (int_k_p(_,_));";
                      on_rez_nonzero
                       "dmap_get_k1_gives_used(map, ikc(user_buf0_34, user_buf0_36, \
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));";
                      on_rez_nonzero
                        "dmap_get_k1_limits(map, ikc(user_buf0_34, user_buf0_36, \
                         user_buf0_26, user_buf0_30, cmplx1, user_buf0_23));";
                      on_rez_nonzero
                       "coherent_dmap_used_dchain_allocated\
                        (map, chain, \
                        dmap_get_k1_fp(map, ikc(user_buf0_34, user_buf0_36, \
                        user_buf0_26, user_buf0_30, cmplx1, user_buf0_23)));";
                      (fun _ _ ->
                         last_index_gotten :=
                           "dmap_get_k1_fp(map, " ^
                           "ikc(user_buf0_34, user_buf0_36, \
                            user_buf0_26, user_buf0_30, cmplx1, user_buf0_23))";
                         "");
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
                        lemmas_after = [
                          (fun _ _ ->
                             "/*@ " ^
                             "{assert double_chainp(?ch, _, _);\n\
                              coherent_dmap_used_dchain_allocated(map, ch," ^
                             !last_index_gotten ^
                             ");\
                              }@*/");];
                        leaks = [
                          "//@ leak flw_p(_,_);";
                          "//@ leak nat_flow_p(_,_,_,_);"];};
     "expire_items", {ret_type = Int;
                      arg_types = [Ptr dchain_struct;
                                   Ptr dmap_struct;
                                   Uint32;];
                      lemmas_before = [];
                      lemmas_after = [
                        (fun rez_var args ->
                           "/*@ if (" ^ rez_var ^ " != 0) {\n" ^
                           "assert dmap_dchain_coherent(?mmmmap, ?ccchhhh);\n\
                            expire_preserves_coherent(mmmmap, ccchhhh, " ^
                           (List.nth_exn args 2) ^ ");\n}@*/");];
                      leaks = [];};
     "dchain_allocate_new_index", {ret_type = Int;
                                   arg_types = [Ptr dchain_struct; Ptr Int; Uint32;];
                                   lemmas_before = [];
                                   lemmas_after = [];
                                   leaks = [];};
     "dchain_rejuvenate_index", {ret_type = Int;
                                 arg_types = [Ptr dchain_struct; Int; Uint32;];
                                 lemmas_before = [];
                                 lemmas_after = [
                                   (fun reg_var args ->
                                      "/*@ if (" ^ reg_var ^ " != 0) {\n" ^
                                      "assert dmap_dchain_coherent(_,?ch);\n" ^
                                      "rejuvenate_preserves_coherent(map, ch, " ^
                                      (List.nth_exn args 1) ^ ", " ^ (List.nth_exn args 2) ^
                                      ");\n}@*/");];
                                 leaks = [];}
    ]
