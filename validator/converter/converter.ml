open Core.Std
open Sexp
open Trace_prefix

type tp = Trace_prefix.trace_prefix

let preamble = In_channel.read_all "preamble.tmpl"

type c_type = | Ptr of c_type
              | Int
              | Uint32
              | Uint16
              | Uint8
              | Void
              | Str of string
              | Ctm of string

let rec c_type_to_str = function
  | Ptr c_type -> c_type_to_str c_type ^ "*"
  | Int -> "int" | Uint32 -> "uint32_t" | Uint16 -> "uint16_t"
  | Uint8 -> "uint8_t" | Void -> "void" | Str name -> "struct " ^ name
  | Ctm name -> name

let is_void = function |Void -> true | _ -> false

type fun_spec = {ret_type: c_type; arg_types: c_type list}

let fun_types =
  String.Map.of_alist_exn
    ["current_time", {ret_type = Uint32;
                      arg_types = []};
     "start_time", {ret_type = Void;
                    arg_types = []};
     "dmap_allocate", {ret_type = Int;
                       arg_types =
                         [Int;Int;Ptr (Ctm "map_keys_equality");
                          Int;Int;Ptr (Ctm "map_keys_equality");
                          Int;Int;Ptr (Ptr (Str "DoubleMap"))];};
     "dmap_set_entry_condition", {ret_type = Void;
                                  arg_types = [Ptr (Ctm "entry_condition")]};
     "dchain_allocate", {ret_type = Int;
                         arg_types = [Int; Ptr (Ptr (Str "DoubleChain"))]};
     "loop_invariant_consume", {ret_type = Void;
                                arg_types = [Ptr (Ptr (Str "DoubleMap"));
                                             Ptr (Ptr (Str "DoubleChain"))]};
     "loop_invariant_produce", {ret_type = Void;
                                arg_types = [Ptr (Ptr (Str "DoubleMap"));
                                             Ptr (Ptr (Str "DoublteChain"))]};
     "loop_enumeration_begin", {ret_type = Void;
                                arg_types = [Int]};
     "loop_enumeration_end", {ret_type = Void;
                              arg_types = []};
     "dmap_get_b", {ret_type = Int;
                   arg_types = [Ptr (Str "DoubleMap"); Ptr Void; Ptr Int;]};
    ]

let get_fun_arg_type fun_name arg_num =
  match String.Map.find fun_types fun_name with
  | Some spec -> List.nth spec.arg_types arg_num
  | None -> None

let get_fun_ret_type fun_name = match String.Map.find fun_types fun_name with
  | Some spec -> Some spec.ret_type
  | None -> None

let to_symbol str =
  let no_spaces = String.substr_replace_all str ~pattern:" " ~with_:"_" in
  let no_sharps = String.substr_replace_all no_spaces ~pattern:"#" ~with_:"num" in
  no_sharps

let get_var_name_of_sexp exp =
  match exp with
  | Sexp.List [Sexp.Atom rd; Sexp.Atom w; Sexp.Atom pos; Sexp.Atom name]
    when String.equal rd "ReadLSB" -> Some (to_symbol name ^ "_" ^ pos ^ w)
  | _ -> None

type var_spec = {name: string; t: c_type option;}

let get_vars tpref =
  let get_vars call =
    let arg_vars = List.foldi call.args ~f:(fun i acc (arg:Trace_prefix.arg) ->
        match get_var_name_of_sexp arg.value.full with
        | Some var_name -> {name = var_name; t = get_fun_arg_type call.fun_name i} :: acc
        | None -> acc
      ) ~init:[] in
    match call.ret with
    | Some ret ->
      begin
        match get_var_name_of_sexp ret.value.full with
        | Some var_name -> {name = var_name; t = get_fun_ret_type call.fun_name} :: arg_vars
        | None -> arg_vars
      end
    | None ->arg_vars in
  let hist_vars = (List.join (List.map tpref.history ~f:(fun call -> get_vars call))) in
  let tip_vars = (List.join (List.map tpref.tip_calls ~f:(fun call -> get_vars call))) in
  List.join [hist_vars; tip_vars]

let render_vars_declarations vars =
  List.fold vars ~init:"" ~f:(fun acc_str v ->
      match v.t with
      | Some t -> acc_str ^ "\n" ^ c_type_to_str t ^ " " ^ v.name ^ ";"
      | None -> acc_str ^ "\n??? " ^ v.name ^ ";" )

let get_val_value valu =
  match valu.full with
  | Sexp.Atom v -> v
  | exp -> match get_var_name_of_sexp exp with
    | Some name -> name
    | None -> "?"

let render_function_list tpref =
  let render_fun_call call =
    let args = List.fold_left call.args ~init:""
        ~f:(fun str_acc arg->
            (if String.equal str_acc "" then "" else str_acc ^ ", ") ^
            get_val_value arg.value) in
    String.concat [call.fun_name; "("; args; ");\n"] in
  let cnt = ref 0 in
  assert (Int.equal 1 (List.length tpref.tip_calls)) ;
  List.fold_left (List.append tpref.history tpref.tip_calls) ~init:""
    ~f:(fun str_acc call ->
        let pre_rend = render_fun_call call in
        match call.ret with
        | Some ret ->
          begin
            let ret_var = "ret" ^ Int.to_string !cnt in
            cnt := !cnt + 1 ;
            match get_fun_ret_type call.fun_name with
            | Some t -> let ret_val = get_val_value ret.value in
              let ret_ass = "//@ assume(" ^ ret_var ^ " == " ^ ret_val ^ ");\n" in
              str_acc ^ c_type_to_str t ^
              " " ^ ret_var ^ " = " ^ pre_rend ^ ret_ass
            | None -> str_acc ^ "??? " ^ ret_var ^ " = " ^ pre_rend
          end
        | None -> str_acc ^ pre_rend
      )

let convert_prefix fin cout =
  Out_channel.output_string cout preamble ;
  Out_channel.output_string cout "void to_verify()/*requires true; */ /* ensures true; */\n{\n" ;
  let pref = Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin) in
  (*Sexp.pp (Format.formatter_of_out_channel cout) (Trace_prefix.sexp_of_trace_prefix pref) ; *)
  Out_channel.output_string cout (render_vars_declarations (get_vars pref)) ;
  Out_channel.newline cout ;
  Out_channel.output_string cout (render_function_list pref) ;
  Out_channel.output_string cout "}\n"

let () =
  convert_prefix "tst.klee" Out_channel.stdout
