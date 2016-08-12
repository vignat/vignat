open Core.Std
open Trace_prefix
open Ir
open Fspec_api

let allocated_args : var_spec String.Map.t ref = ref String.Map.empty

let infer_signed_type w =
  if String.equal w "w32" then Sint32
  else if String.equal w "w8" then Sint8
  else Sunknown
  (* TODO: this computation is sometimes is not necessary,
     so this exception may break a problem free insuction.
     else failwith (w ^ " signed is not supported")*)

let infer_unsigned_type w =
  if String.equal w "w32" then Uint32
  else if String.equal w "w16" then Uint16
  else if String.equal w "w8" then Uint8
  else failwith (w ^ " unsigned is not supported")

let infer_type_class f =
  if String.equal f "Sle" then Sunknown
  else if String.equal f "Slt" then Sunknown
  else if String.equal f "Ule" then Uunknown
  else if String.equal f "Ult" then Uunknown
  else Unknown

let expand_shorted_sexp sexp =
  let rec get_defs sexp =
    let merge_defs d1 d2 =
      String.Map.merge d1 d2
        ~f:(fun ~key pres ->
            ignore key;
            match pres with
            | `Both (_,_) -> failwith "double definition"
            | `Left x -> Some x
            | `Right x -> Some x)
    in
    let rec do_list lst =
      match lst with
      | Sexp.Atom v :: def :: tl when String.is_suffix v ~suffix:":" ->
        merge_defs (get_defs def) (String.Map.add (do_list tl)
                                     ~key:(String.prefix v ((String.length v) - 1))
                                     ~data:def)
      | hd :: tl -> merge_defs (get_defs hd) (do_list tl)
      | [] -> String.Map.empty
    in
    match sexp with
    | Sexp.List lst -> do_list lst
    | Sexp.Atom _ -> String.Map.empty
  in
  let rec remove_defs exp =
    let rec do_list lst =
      match lst with
      | Sexp.Atom v :: tl when String.is_suffix v ~suffix:":" ->
        do_list tl
      | hd :: tl -> (remove_defs hd) :: (do_list tl)
      | [] -> []
    in
    match exp with
    | Sexp.List lst -> Sexp.List (do_list lst)
    | Sexp.Atom _ -> exp
  in
  let rec expand_exp exp vars =
    match exp with
    | Sexp.List lst ->
      let (expaneded_lst,smth_changed) =
        List.fold_left lst ~init:([],false)
          ~f:(fun (prev_expanded,prev_changed) el ->
              let (expanded,changed) = expand_exp el vars in
              (expanded::prev_expanded,changed||prev_changed))
      in
      (Sexp.List (List.rev expaneded_lst),smth_changed)
    | Sexp.Atom str -> match String.Map.find vars str with
      | Some ex -> (ex,true)
      | None -> (exp,false)
  in
  let expand_map map defs =
    String.Map.map map ~f:(fun el ->
        let (new_el, _) = expand_exp el defs in new_el)
  in
  let map_non_expandable map defs =
    not (List.exists (String.Map.data map) ~f:(fun el -> (snd (expand_exp el defs))))
  in
  let defs = get_defs sexp in
  let defs = expand_map defs defs in
  assert(map_non_expandable defs defs);
  (fst (expand_exp (remove_defs sexp) defs))

let get_fun_arg_type ftype_of fun_name arg_num =
  List.nth_exn (ftype_of fun_name).arg_types arg_num

let get_fun_ret_type ftype_of fun_name = (ftype_of fun_name).ret_type

let to_symbol str =
  let no_spaces = String.substr_replace_all str ~pattern:" " ~with_:"_" in
  let no_octotorps = String.substr_replace_all no_spaces ~pattern:"#" ~with_:"num" in
  no_octotorps

let get_var_name_of_sexp exp =
  match exp with
  | Sexp.List [Sexp.Atom rd; Sexp.Atom _; Sexp.Atom pos; Sexp.Atom name]
    when ( String.equal rd "ReadLSB" ||
           String.equal rd "Read") -> Some (to_symbol name ^ "_" ^
                                            pos(* FIXME: '^ w' - this reveals a bug where
                                               allocated_dmap appears to be w32 and w64*))
  | _ -> None

let get_read_width_of_sexp exp =
  match exp with
  | Sexp.List [Sexp.Atom rd; Sexp.Atom w; Sexp.Atom _; Sexp.Atom _]
    when (String.equal rd "ReadLSB" ||
          String.equal rd "Read") -> Some w
  | _ -> None

let determine_type t w =
  match t with
  | Sunknown -> infer_signed_type w
  | Uunknown -> infer_unsigned_type w
  | _ -> t

let map_set_n_update_alist mp lst =
  List.fold lst ~init:mp ~f:(fun acc (key,data) ->
      String.Map.add acc ~key ~data)

let is_int str =
  try ignore (int_of_string str); true
  with _ -> false

let guess_type exp =
  match exp with
  | Sexp.Atom str ->
    if (String.equal str "true") ||
       (String.equal str "false") then Boolean
    else if is_int str then Sint32 (*TODO: set uint for out-of-signed-range value*)
    else Unknown
  | _ -> Unknown

let rec guess_type_l exps =
  match exps with
  | hd :: tl -> begin match guess_type hd with
      | Unknown -> guess_type_l tl
      | t -> t
    end
  | [] -> Unknown

let update_var_spec (spec:var_spec) v =
  let t_final = match spec.value.t with
    | Unknown -> v.t
    | Sunknown | Uunknown -> if v.t = Unknown then spec.value.t else v.t
    | _ -> spec.value.t in
  let v_final = match spec.value.v with
    | Undef -> v.v
    | _ -> spec.value.v in
  {name = spec.name;
   value = {v=v_final; t=t_final};}

let failback_type t1 t2 =
  match t1 with
  | Unknown -> t2
  | _ -> t1

let rec get_var_decls_of_sexp exp t known_vars =
  match get_var_name_of_sexp exp, get_read_width_of_sexp exp with
  | Some name, Some w ->
    begin match String.Map.find known_vars name with
      | Some spec -> [update_var_spec spec {v=Undef;t=(determine_type t w)}]
      | None -> [{name = name; value={v=Undef;t=determine_type t w}}]
    end
  | None, None ->
    begin
    match exp with
    | Sexp.List (Sexp.Atom f :: Sexp.Atom w :: tl)
      when (String.equal w "w32") || (String.equal w "w16") || (String.equal w "w8") ->
      let ty = failback_type (determine_type (infer_type_class f) w) t in
      (List.join (List.map tl ~f:(fun e -> get_var_decls_of_sexp e ty known_vars)))
    | Sexp.List (Sexp.Atom f :: tl) ->
      let ty = failback_type (infer_type_class f)
          (failback_type (guess_type_l tl) t)
      in
      List.join (List.map tl ~f:(fun e -> get_var_decls_of_sexp e ty known_vars))
    | _ -> []
    end
  | _,_ -> failwith "inconsistency in get_var_name/get_read_width"

let make_name_alist_from_var_decls (lst: var_spec list) =
  List.map lst ~f:(fun x -> (x.name,x))

let get_vars_from_plain_val v ty known_vars =
  (*TODO: proper type induction here, e.g. Sadd w16 -> Sint16, ....*)
  let decls = get_var_decls_of_sexp v ty known_vars in
  map_set_n_update_alist known_vars (make_name_alist_from_var_decls decls)


let rec get_vars_from_struct_val v ty known_vars =
  match ty with
  | Str (name, fields) ->
    let ftypes = List.map fields ~f:snd in
    if (List.length v.break_down) <>
       (List.length fields)
    then
      failwith ("Mismatch between expected and traced breakdowns for " ^
                name ^ ".")
    else
      List.fold (List.zip_exn v.break_down ftypes) ~init:known_vars
        ~f:(fun acc (v,t)->
          get_vars_from_struct_val v.value t acc)
  | ty ->
    get_vars_from_plain_val v.full ty known_vars

let name_gen prefix = object
  val mutable cnt = 0
  method generate =
    cnt <- cnt + 1 ;
    prefix ^ Int.to_string cnt
end

let complex_val_name_gen = name_gen "cmplx"
let allocated_complex_vals : var_spec String.Map.t ref = ref String.Map.empty

let tmp_val_name_gen = name_gen "tmp"
let allocated_tmp_vals = ref String.Map.empty

let get_sint_in_bounds v =
  let integer_val = Int.of_string v in
  if Int.(integer_val > 2147483647) then
    integer_val - 2*2147483648
  else
    integer_val

let make_cmplx_val exp t =
  let key = Sexp.to_string exp in
  match String.Map.find !allocated_complex_vals key with
  | Some v -> v.value
  | None ->
    let name = complex_val_name_gen#generate in
    let value = {v=Id name;t} in
    allocated_complex_vals :=
      String.Map.add !allocated_complex_vals ~key
        ~data:{name;value};
    value

let allocate_tmp value =
  let key = (render_tterm value) in
  match String.Map.find !allocated_tmp_vals key with
  | Some {name;value} -> {v=Id name;t=value.t}
  | None ->
    let name = tmp_val_name_gen#generate in
    allocated_tmp_vals :=
      String.Map.add !allocated_tmp_vals
        ~key
        ~data:{name; value};
    {v=Id name;t=value.t}

(*TODO: rewrite this in terms of my IR instead of raw Sexps*)
let eliminate_false_eq_0 exp t =
  match (exp,t) with
  | Sexp.List [Sexp.Atom eq1; Sexp.Atom fls;
               Sexp.List [Sexp.Atom eq2; Sexp.Atom zero; e]],
    Boolean
    when (String.equal eq1 "Eq") && (String.equal fls "false") &&
         (String.equal eq2 "Eq") && (String.equal zero "0") ->
    e
  | _ -> exp

let is_bool_fun fname =
  if String.equal fname "Eq" then true
  else if String.equal fname "Sle" then true
  else if String.equal fname "Slt" then true
  else if String.equal fname "Ule" then true
  else if String.equal fname "Ult" then true
  else false

let rec is_bool_expr exp =
  match exp with
  | Sexp.List [Sexp.Atom f; _; _] when is_bool_fun f -> true
  | Sexp.List [Sexp.Atom a; _; lhs; rhs] when String.equal a "And" ->
    (*FIXME: and here, but really that is a bool expression, I know it*)
    (is_bool_expr lhs) || (is_bool_expr rhs)
  | Sexp.List [Sexp.Atom ext; _; e] when String.equal ext "ZExt" ->
    is_bool_expr e
  | _ -> false

let rec get_sexp_value exp t =
  let exp = expand_shorted_sexp exp in
  let exp = eliminate_false_eq_0 exp t in
  match exp with
  | Sexp.Atom v ->
    begin
      let t = match t with Unknown|Sunknown|Uunknown ->
        guess_type exp |_->t
      in
      match t with
      | Sint32 -> {v=Int (get_sint_in_bounds v);t}
      | Boolean ->
        if String.equal v "true" then {v=Bool true;t}
        else if String.equal v "false" then {v=Bool false;t}
        else {v=Id v; t}
      | _ -> {v=Id v;t}
    end
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; Sexp.Atom offset; src;]
    when (String.equal f "Extract") && (String.equal offset "0") ->
    (*FIXME: make sure the typetransformation works.*)
    (*FIXME: pass a right type to get_sexp_value and llocate_tmp here*)
    {v=Cast (t, allocate_tmp (get_sexp_value src Sint32));t}
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "Add") ->
    begin (* Prefer a variable in the left position
             due to the weird VeriFast type inference rules.*)
      match lhs with
      | Sexp.Atom str when is_int str ->
        let ival = int_of_string str in (* avoid overflow *)
        if ival > 2147483648 then
          {v=Bop (Sub,(get_sexp_value rhs t),{v=(Int (2*2147483648 - ival));t});t}
        else
          {v=Bop (Add,(get_sexp_value rhs t),{v=(Int ival);t});t}
      | _ ->
        {v=Bop (Add,(get_sexp_value lhs t),(get_sexp_value rhs t));t}
    end
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Slt") ->
    (*FIXME: get the actual type*)
    {v=Bop (Lt,(get_sexp_value lhs Sunknown),(get_sexp_value rhs Sunknown));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Sle") ->
    (*FIXME: get the actual type*)
    {v=Bop (Le,(get_sexp_value lhs Sunknown),(get_sexp_value rhs Sunknown));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Ule") ->
    (*FIXME: get the actual type*)
    {v=Bop (Le,(get_sexp_value lhs Uunknown),(get_sexp_value rhs Uunknown));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Ult") ->
    {v=Bop (Lt,(get_sexp_value lhs Uunknown),(get_sexp_value rhs Uunknown));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Eq") ->
    let ty = guess_type_l [lhs;rhs] in
    {v=Bop (Eq,(get_sexp_value lhs ty),(get_sexp_value rhs ty));t}
  | Sexp.List [Sexp.Atom f; _; e]
    when String.equal f "ZExt" ->
    (*TODO: something smarter here.*)
    get_sexp_value e t
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "And") &&
         ((is_bool_expr lhs) || (is_bool_expr rhs)) ->
    (*FIXME: and here, but really that is a bool expression, I know it*)
    (*TODO: check t is really Boolean here*)
    {v=Bop (And,(get_sexp_value lhs Boolean),(get_sexp_value rhs Boolean));t}
  | _ ->
    begin match get_var_name_of_sexp exp with
      | Some name -> {v=Id name;t}
      | None -> make_cmplx_val exp t
    end

let rec get_struct_val_value valu t =
  match t with
  | Str (strname, fields) ->
    begin
    (*   match get_var_name_of_sexp valu.full with *)
    (* | Some name -> {v=Id name;t} *)
    (* | None -> <^^^ this was working a while ago, may be it should be
       left somewhere *)
      let fields = List.map2_exn valu.break_down fields
          ~f:(fun {fname;value} (name,t) ->
              assert(String.equal name fname);
              {name;value=(get_struct_val_value value t)})
      in
      {v=Struct (strname, fields);t}
    end
  | _ -> get_sexp_value valu.full t

let get_vars ftype_of tpref arg_name_gen =
  let get_vars known_vars call =
    let alloc_local_arg addr value =
      match String.Map.find !allocated_args addr with
      | None ->
        let p_name = arg_name_gen#generate in
        allocated_args := String.Map.add !allocated_args
            ~key:addr ~data:{name = p_name;
                             value};
      | Some spec ->
        allocated_args := String.Map.add !allocated_args
            ~key:addr ~data:(update_var_spec spec value)
    in
    let get_arg_pointee_vars addr ptee ptee_type accumulator =
      let before_vars = match ptee.before with
        | Some v ->
          alloc_local_arg addr (get_struct_val_value v ptee_type);
          get_vars_from_struct_val v ptee_type accumulator
        | None -> failwith("initial argument pointee value must" ^
                           " be dumped for call " ^ call.fun_name)
      in
      get_vars_from_struct_val ptee.after ptee_type before_vars;
    in
    let get_ret_pointee_vars addr ptee ptee_type accumulator =
      assert(ptee.before = None);
      (*TODO: use another name generator to distinguish
        ret pointee stubs from the args *)
      alloc_local_arg addr (get_struct_val_value ptee.after ptee_type);
      get_vars_from_struct_val ptee.after ptee_type accumulator;
    in
    let complex_value_vars value ptr t is_ret acc =
      match ptr with
      | Nonptr -> get_vars_from_plain_val value t acc
      | Funptr _ -> acc
      | Apathptr ->
        let addr = (Sexp.to_string value) in
        let ptee_type = get_pointee t in
        alloc_local_arg addr {v=Undef;t=ptee_type};
        acc
      | Curioptr ptee ->
        let addr = (Sexp.to_string value) in
        let ptee_type = get_pointee t in
        if is_ret then get_ret_pointee_vars addr ptee ptee_type acc
        else get_arg_pointee_vars addr ptee ptee_type acc
    in
    let arg_vars = List.foldi call.args ~init:known_vars
        ~f:(fun i acc arg ->
            let arg_type = get_fun_arg_type ftype_of call.fun_name i in
            complex_value_vars arg.value arg.ptr arg_type false acc)
    in
    let ret_vars = match call.ret with
      | Some ret ->
        complex_value_vars
          ret.value ret.ptr
          (get_fun_ret_type ftype_of call.fun_name) true arg_vars
      | None -> arg_vars in
    let add_vars_from_ctxt vars ctxt =
      map_set_n_update_alist vars
        (make_name_alist_from_var_decls
           (get_var_decls_of_sexp ctxt Boolean vars)) in
    let call_ctxt_vars =
      List.fold call.call_context ~f:add_vars_from_ctxt ~init:ret_vars in
    let ret_ctxt_vars =
      List.fold call.ret_context ~f:add_vars_from_ctxt ~init:call_ctxt_vars in
    ret_ctxt_vars
  in
  let hist_vars = (List.fold tpref.history ~init:String.Map.empty
                     ~f:get_vars) in
  let tip_vars = (List.fold tpref.tip_calls ~init:hist_vars
                    ~f:get_vars) in
  tip_vars

let compose_fcall_preamble ftype_of call args tmp_gen =
  (List.map (ftype_of call.fun_name).lemmas_before ~f:(fun l -> l args tmp_gen))

let extract_fun_args ftype_of call =
  let get_allocated_arg (arg: Trace_prefix.arg) arg_type =
    let arg_var = String.Map.find !allocated_args
        ( Sexp.to_string arg.value) in
    let ptee_t = get_pointee arg_type in
    match arg_var with
    | Some n -> {v=Addr {v=(Id n.name);t=ptee_t};t=arg_type}
    | None -> {v=Addr {v=(Id "arg??");t=ptee_t};t=arg_type}
  in
  List.mapi call.args
    ~f:(fun i arg ->
        let a_type = get_fun_arg_type ftype_of call.fun_name i in
        match arg.ptr with
        | Nonptr -> get_sexp_value arg.value a_type
        | Funptr fname -> {v=Fptr fname;t=a_type}
        | Apathptr ->
          get_allocated_arg arg a_type
        | Curioptr ptee ->
          get_allocated_arg arg a_type)

let compose_post_lemmas ftype_of call ret_name args tmp_gen =
  let ret_name = match ret_name with
    | Some ret_name -> ret_name
    | None -> ""
  in
  List.map (ftype_of call.fun_name).lemmas_after
    ~f:(fun l -> l ret_name args tmp_gen)

let compose_args_post_conditions call =
  List.filter_map call.args ~f:(fun arg ->
      match arg.ptr with
      | Nonptr -> None
      | Funptr _ -> None
      | Apathptr -> None
      | Curioptr ptee ->
        let out_arg =
          let key = Sexp.to_string arg.value in
          String.Map.find_exn !allocated_args key
        in
        Some {name=out_arg.name;
              value=(get_struct_val_value ptee.after out_arg.value.t)})

let extract_tip_ret_post_conditions call =
  List.map call.ret_context ~f:(fun sttmt ->
      get_sexp_value sttmt Boolean)

let get_ret_val ftype_of call =
  match call.ret with
  | Some ret ->
    let t = get_fun_ret_type ftype_of call.fun_name in
    get_sexp_value ret.value t
  | None -> {v=Undef;t=Unknown}

let gen_unique_tmp_name unique_postfix prefix =
  prefix ^ unique_postfix

let extract_common_call_context ftype_of call ret_name args unique_postfix =
  let tmp_gen = gen_unique_tmp_name unique_postfix in
  let ret_type = get_fun_ret_type ftype_of call.fun_name in
  let arg_names = List.map args ~f:render_tterm in
  let pre_lemmas = compose_fcall_preamble ftype_of call arg_names tmp_gen in
  let application = Apply (call.fun_name,args) in
  let post_lemmas = compose_post_lemmas ftype_of call ret_name arg_names tmp_gen in
  {pre_lemmas;application;post_lemmas;ret_name;ret_type}

let extract_hist_call_context ftype_of call rname_gen index =
  let ret_name = if is_void (get_fun_ret_type ftype_of call.fun_name) then None
    else Some rname_gen#generate in
  let args = extract_fun_args ftype_of call in
  let args_post_conditions = compose_args_post_conditions call in
  {context=extract_common_call_context ftype_of call ret_name args
       (string_of_int index);
   result={args_post_conditions;ret_val=get_ret_val ftype_of call;
           post_statements=[]}}

let tip_calls_context ftype_of calls rname_gen =
  let call = List.hd_exn calls in
  let ret_name = if is_void (get_fun_ret_type ftype_of call.fun_name) then None
    else Some rname_gen#generate in
  let args = extract_fun_args ftype_of call in
  let context = extract_common_call_context ftype_of call ret_name args "tip" in
  let results = List.map calls ~f:(fun call ->
      let args_post_conditions = compose_args_post_conditions call in
      {args_post_conditions;
       ret_val=get_ret_val ftype_of call;
       post_statements=(extract_tip_ret_post_conditions call);})
  in
  {context;results}

let extract_calls_info ftype_of tpref =
  let rez_gen = name_gen "rez" in
  let hist_funs =
    (List.mapi tpref.history ~f:(fun ind call ->
         extract_hist_call_context ftype_of call rez_gen ind))
  in
  let tip_calls = tip_calls_context ftype_of tpref.tip_calls rez_gen in
  hist_funs, tip_calls

let collect_context pref =
  let collect_ctxt_list l = List.map l ~f:(fun e ->
      (get_sexp_value e Boolean))
  in
  (List.join (List.map pref.history ~f:(fun call ->
      (collect_ctxt_list call.call_context) @
      (collect_ctxt_list call.ret_context)))) @
  (match pref.tip_calls with
   | hd :: _ -> (collect_ctxt_list hd.call_context)
   | [] -> failwith "Must have at least one tip call.")

let extract_leaks ftype_of ccontexts =
  let leak_map =
    List.fold ccontexts ~init:String.Map.empty ~f:(fun acc {ret_name;application;_} ->
        match application with
        | Apply (fname,args) ->
          let args = List.map args ~f:render_tterm in
          let spec = (ftype_of fname) in
          let ret_name = match ret_name with Some name -> name | None -> "" in
          List.fold spec.leaks ~init:acc ~f:(fun acc l ->
              l ret_name args acc)
        | _ -> failwith "call context application must be Apply")
  in
  String.Map.data leak_map

let strip_context call =
  {fun_name = call.fun_name; args = call.args;
   ret = None; call_context = []; ret_context = []}

let get_relevant_segment pref boundary_fun =
  let rec last_relevant_seg hist candidat =
    match hist with
    | c :: rest ->
      if (String.equal c.fun_name boundary_fun) then
        last_relevant_seg rest hist
      else
        last_relevant_seg rest candidat
    | [] -> candidat
  in
  match pref.tip_calls with
  | [] -> failwith "must have at least one tip call."
  | hd :: _ ->
    if (String.equal hd.fun_name boundary_fun) then
      {history=[]; tip_calls = List.map pref.tip_calls strip_context}
    else
      match last_relevant_seg pref.history [] with
      | bnd :: rest ->
        {history = strip_context bnd :: rest; tip_calls = pref.tip_calls}
      | [] -> pref

let build_ir fun_types fin preamble boundary_fun =
  let ftype_of fun_name =
    match String.Map.find fun_types fun_name with
    | Some spec -> spec
    | None -> failwith ("unknown function " ^ fun_name)
  in
  let pref = get_relevant_segment
      (Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin))
      boundary_fun
  in
  let preamble = preamble ^
                 "void to_verify()\
                  /*@ requires true; @*/ \
                  /*@ ensures true; @*/\n{\n" in
  let export_point = "export_point" in
  let free_vars = get_vars ftype_of pref (name_gen "arg") in
  let (hist_calls,tip_call) = extract_calls_info ftype_of pref in
  let leaks = extract_leaks ftype_of
      ((List.map hist_calls ~f:(fun hc -> hc.context))@[tip_call.context]) in
  let cmplxs = !allocated_complex_vals in
  let tmps = !allocated_tmp_vals in
  let context_assumptions = collect_context pref in
  let arguments = !allocated_args in
  {preamble;free_vars;arguments;tmps;
   cmplxs;context_assumptions;hist_calls;tip_call;
   leaks;export_point}
