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

let is_void = function | Void -> true | _ -> false

let get_pointee = function | Ptr t -> t | _ -> failwith "not a plain pointer"

type fun_spec = {ret_type: c_type; arg_types: c_type list;
                 lemmas_before: string list; lemmas_after: string list;
                 leaks: string list;}

let dmap_struct = Str ( "DoubleMap", [] )
let dchain_struct = Str ( "DoubleChain", [] )
let ext_key_struct = Str ( "ext_key", ["ext_src_port", Uint16;
                                       "dst_port", Uint16;
                                       "ext_src_ip", Uint32;
                                       "dst_ip", Uint32;
                                       "ext_device_id", Uint8;
                                       "protocol", Uint8;] )

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
                                lemmas_after = ["//@ open evproc_loop_invariant(?mp, ?chp);"];
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
                    "//@ open (ext_k_p(_,_));"];
                    leaks = [];};
    ]
