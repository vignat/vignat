open Core.Std
open Sexp
open Trace_prefix
open Function_spec

type tp = Trace_prefix.trace_prefix

let preamble = In_channel.read_all "preamble.tmpl"

type var_spec = {name: string; t: c_type; v: struct_val option}

let allocated_args : var_spec String.Map.t ref = ref String.Map.empty

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
    when ( String.equal rd "ReadLSB" ||
           String.equal rd "Read") -> Some (to_symbol name ^ "_" ^
                                            pos(* FIXME: '^ w' - this reveals a bug where
                                               allocated_dmap appears to be w32 and w64*))
  | _ -> None

let rec get_vars_from_struct_val v ty =
  match ty with
  | Str (_, fields) ->
    let ftypes = List.map fields ~f:snd in
    List.join (List.map2_exn v.break_down ftypes ~f:(fun v t -> get_vars_from_struct_val v.value t))
  | ty ->
    begin
      match get_var_name_of_sexp v.full with
      | Some var_name -> [{name = var_name;
                           t = ty;
                           v = None}]
      | None -> []
    end

let get_vars tpref arg_name_gen =
  let get_vars call =
    let arg_vars = List.foldi call.args ~f:(fun i acc (arg:Trace_prefix.arg) ->
        if arg.is_ptr then
          match arg.pointee with
          | Some ptee ->
            begin
              if ptee.is_fun_ptr then
                acc
              else
              if String.Map.mem !allocated_args (Sexp.to_string arg.value.full) then
                acc
              else
                let ty =
                  Option.map (get_fun_arg_type call.fun_name i) ~f:get_pointee
                in
                let p_name = arg_name_gen#generate in
                let ptr = match ty with | Some t ->
                  {name = p_name;
                   t = t;
                   v = ptee.before}
                                        | None -> failwith ("no type for " ^ p_name)
                in
                allocated_args := String.Map.add !allocated_args
                    ~key:(Sexp.to_string arg.value.full) ~data:ptr ;
                let before_vars =
                  match ptee.before with
                  | Some v ->
                    begin
                      match ty with
                      | Some t -> get_vars_from_struct_val v t
                      | None -> failwith ( "no type defined for the value" ^ Sexp.to_string v.full )
                    end
                  | None -> ptr :: acc
                in
                let after_vars =
                  match ptee.after with
                  | Some v ->
                    begin
                    match ty with
                    | Some t -> get_vars_from_struct_val v t
                    | None -> failwith ("no type defined for the value" ^ Sexp.to_string v.full)
                    end
                  | None -> []
                in
                List.join [before_vars; [ptr]; after_vars; acc]
            end
          | None -> acc
        else
          match get_var_name_of_sexp arg.value.full with
          | Some var_name -> begin match get_fun_arg_type call.fun_name i with
            | Some t -> {name = var_name;
                         t = t;
                         v = None} :: acc
            | None -> failwith ("no type for " ^ var_name)
            end
          | None -> acc
      ) ~init:[]
    in
    match call.ret with
    | Some ret ->
      begin
        match get_var_name_of_sexp ret.value.full with
        | Some var_name -> begin match get_fun_ret_type call.fun_name with
            | Some t -> {name = var_name;
                         t = t;
                         v = None} :: arg_vars
            | None -> failwith ("no type for " ^ var_name)
          end
        | None -> arg_vars
      end
    | None -> arg_vars in
  let hist_vars = (List.join (List.map tpref.history ~f:(fun call -> get_vars call))) in
  let tip_vars = (List.join (List.map tpref.tip_calls ~f:(fun call -> get_vars call))) in
  List.join [hist_vars; tip_vars]

let name_gen prefix = object
  val mutable cnt = 0

  method generate =
    cnt <- cnt + 1 ;
    prefix ^ Int.to_string cnt
end

let allocated_complex_vals = ref String.Map.empty
let complex_val_name_gen = name_gen "cmplx"

let put_in_int_bounds v =
  let integer_val = Int.of_string v in
  if Int.(integer_val > 2147483647) then
    Int.to_string (integer_val - 2*2147483648)
  else
    Int.to_string integer_val

let get_val_value valu t =
  match valu.full with
  | Sexp.Atom v ->
    begin
      match t with
      | Some t -> begin match t with
          | Int -> put_in_int_bounds v
          | _ -> v
        end
      | None -> v
    end
  | exp ->
    begin match get_var_name_of_sexp exp with
      | Some name -> name
      | None ->
        let key = Sexp.to_string exp in
        match String.Map.find !allocated_complex_vals key with
          | Some v -> v.name
          | None ->
            match t with
              | Some t ->
                let name = complex_val_name_gen#generate in
                allocated_complex_vals :=
                  String.Map.add !allocated_complex_vals ~key
                    ~data:{name = name;
                           t = t;
                           v = Some valu;} ;
                name
              | None -> key
    end

let rec render_assignment var_name var_value var_type =
  match var_value with
  | Some v ->
    begin match var_type with
      | Str (_, fields) ->
        let fts = List.map fields ~f:snd in
        String.concat (List.map2_exn v.break_down fts ~f:(fun f ft ->
            render_assignment (var_name ^ "." ^ f.name) (Some f.value) ft))
      | _ ->
        var_name ^ " = " ^ (get_val_value v (Some var_type)) ^ ";\n"
    end
  | None -> ""

let render_vars_declarations vars =
  List.fold vars ~init:"\n" ~f:(fun acc_str v ->
      acc_str ^ c_type_to_str v.t ^ " " ^ v.name ^ ";\n")

let render_var_assignments vars =
  List.fold vars ~init:"\n" ~f:(fun acc_str v ->
      acc_str ^ (render_assignment v.name v.v v.t))

let rec render_eq_sttmt head out_arg out_val out_t =
  match out_t with
  | Str (_, fields) -> let f_types = List.map fields ~f:snd in
    String.concat (List.map2_exn out_val.break_down f_types ~f:(fun f ft ->
        render_eq_sttmt head (out_arg ^ "." ^ f.name) f.value ft))
  | _ -> "//@ " ^ head ^ "(" ^ out_arg ^ " == " ^ (get_val_value out_val (Some out_t)) ^ ");\n"


let render_fun_call_in_context call rname_gen is_tip =
  let render_fun_call call =
    let args = List.fold_left call.args ~init:""
        ~f:(fun str_acc arg ->
            (if String.equal str_acc "" then "" else str_acc ^ ", ") ^
            ( if arg.is_ptr then
                match arg.pointee with
                | Some ptee ->
                  begin
                    if ptee.is_fun_ptr then
                      match ptee.fun_name with
                      | Some n -> n
                      | None -> "fun???"
                    else
                      let arg_name = String.Map.find !allocated_args
                          ( Sexp.to_string arg.value.full ) in
                      match arg_name with
                      | Some n -> "&" ^ n.name
                      | None -> "&arg??"
                  end
                | None -> "???"
            else
              get_val_value arg.value None )) in
    String.concat [call.fun_name; "("; args; ");\n"] in
  let pre_rend = render_fun_call call in
  let (pre_lemmas,post_lemmas) =
    match String.Map.find fun_types call.fun_name with
    | Some t -> ((String.concat ~sep:"\n" t.lemmas_before) ^ "\n",
                (String.concat ~sep:"\n" t.lemmas_after) ^ "\n")
    | None -> failwith "" in
  let call_with_ret = match call.ret with
    | Some ret ->
      begin
        let ret_var = rname_gen#generate in
        match get_fun_ret_type call.fun_name with
        | Some t -> let ret_val = get_val_value ret.value None in
          let ret_ass = "//@ " ^ (if is_tip then "assert" else "assume") ^
                        "(" ^ ret_var ^ " == " ^ ret_val ^ ");\n" in
          c_type_to_str t ^ " " ^ ret_var ^ " = " ^ pre_rend ^ ret_ass
        | None -> "??? " ^ ret_var ^ " = " ^ pre_rend
      end
    | None -> pre_rend
  in
  let post_statements =
    let sttmts = List.map call.args ~f:(fun arg ->
        if arg.is_ptr then
          match arg.pointee with
          | Some ptee ->
            if ptee.is_fun_ptr then ""
            else begin
              match ptee.after with
              | Some v ->
                let out_arg =
                  match String.Map.find !allocated_args (Sexp.to_string arg.value.full) with
                  | Some out_arg -> out_arg
                  | None -> failwith ( "unknown argument for " ^ (Sexp.to_string arg.value.full))
                in
                render_eq_sttmt (if is_tip then "assert" else "assume") out_arg.name v out_arg.t
              | None -> ""
            end
          | None -> ""
        else "")
    in
    String.concat sttmts
  in
  pre_lemmas ^ call_with_ret ^ post_lemmas ^ post_statements


let render_function_list tpref =
  let rez_gen = name_gen "rez" in
  assert (Int.equal 1 (List.length tpref.tip_calls)) ;
  (List.fold_left tpref.history ~init:""
     ~f:(fun str_acc call ->
         str_acc ^ render_fun_call_in_context call rez_gen false
       )) ^
   (render_fun_call_in_context (List.hd_exn tpref.tip_calls) rez_gen true)

let render_cmplxes () =
  String.concat (List.map (String.Map.data !allocated_complex_vals) ~f:(fun var ->
      ((c_type_to_str var.t) ^ " " ^ var.name ^ ";") ^
      (match var.v with
       | Some v -> " //=" ^ (Sexp.to_string v.full) ^ "\n"
       | None -> "\n")))

let rec get_relevant_segment pref =
  match List.findi pref.history ~f:(fun _ call ->
      String.equal call.fun_name "loop_invariant_consume") with
  | Some (pos,_) ->
    let tail_len = (List.length pref.history) - pos - 1 in
    get_relevant_segment
      {history = List.sub pref.history ~pos:(pos + 1) ~len:tail_len;
       tip_calls = pref.tip_calls;}
  | None -> pref

let convert_prefix fin cout =
  Out_channel.output_string cout preamble ;
  Out_channel.output_string cout "void to_verify()\
                                  /*@ requires true; @*/ \
                                  /*@ ensures true; @*/\n{\n" ;
  let pref = get_relevant_segment
      (Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin)) in
  let vars = (List.dedup (get_vars pref (name_gen "arg"))) in
  let var_decls = (render_vars_declarations vars) in
  let var_assigns = (render_var_assignments vars) in
  let fun_calls = (render_function_list pref) in
  Out_channel.output_string cout ( render_cmplxes () ) ;
  Out_channel.output_string cout var_decls;
  Out_channel.output_string cout var_assigns;
  Out_channel.newline cout ;
  Out_channel.output_string cout fun_calls;
  Out_channel.output_string cout "}\n"

let () =
  Out_channel.with_file Sys.argv.(2) ~f:(fun fout ->
      convert_prefix Sys.argv.(1) fout
    )
