open Core.Std
open Trace_prefix
open Ir

module Fs = Function_spec

let preamble = In_channel.read_all "preamble.tmpl"

let allocated_args : var_spec String.Map.t ref = ref String.Map.empty

let infer_signed_type w =
  if String.equal w "w32" then Sint32
  else if String.equal w "w8" then Sint8
  else failwith (w ^ " signed is not supported")

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

let get_fun_arg_type fun_name arg_num =
  match String.Map.find Fs.fun_types fun_name with
  | Some spec -> List.nth_exn spec.Fs.arg_types arg_num
  | None -> failwith ("unknown function " ^ fun_name)

let get_fun_ret_type fun_name = match String.Map.find Fs.fun_types fun_name with
  | Some spec -> spec.Fs.ret_type
  | None -> failwith ("unknown function " ^ fun_name)

let to_symbol str =
  let no_spaces = String.substr_replace_all str ~pattern:" " ~with_:"_" in
  let no_octotorps = String.substr_replace_all no_spaces ~pattern:"#" ~with_:"num" in
  no_octotorps

let get_var_name_of_sexp exp =
  match exp with
  | Sexp.List [Sexp.Atom rd; Sexp.Atom w; Sexp.Atom pos; Sexp.Atom name]
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

let rec get_vars_from_struct_val v ty known_vars =
  match ty with
  | Str (_, fields) ->
    let ftypes = List.map fields ~f:snd in
    if (List.length v.break_down) = 0 then
      failwith "unreported structure breakdown."
    else
      List.fold (List.zip_exn v.break_down ftypes) ~init:known_vars
        ~f:(fun acc (v,t)->
          get_vars_from_struct_val v.value t acc)
  | ty ->
    (*TODO: proper type induction here, e.g. Sadd w16 -> Sint16, ....*)
    let decls = get_var_decls_of_sexp v.full ty known_vars in
    map_set_n_update_alist known_vars (make_name_alist_from_var_decls decls)

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
  | Sexp.List [Sexp.Atom a; w; lhs; rhs] when String.equal a "And" ->
    (*FIXME: and here, but really that is a bool expression, I know it*)
    (is_bool_expr lhs) || (is_bool_expr rhs)
  | Sexp.List [Sexp.Atom ext; w; e] when String.equal ext "ZExt" ->
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
  | Sexp.List [Sexp.Atom f; Sexp.Atom w; Sexp.Atom offset; src;]
    when (String.equal f "Extract") && (String.equal offset "0") ->
    (*FIXME: make sure the typetransformation works.*)
    (*FIXME: pass a right type to get_sexp_value and llocate_tmp here*)
    {v=Cast (t, allocate_tmp (get_sexp_value src Sint32));t}
  | Sexp.List [Sexp.Atom f; Sexp.Atom w; lhs; rhs]
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
  | Str (strname, fields) -> begin match get_var_name_of_sexp valu.full with
    | Some name -> {v=Id name;t}
    | None ->
      let fields = List.map2_exn valu.break_down fields
          ~f:(fun {fname;value} (name,t) ->
              assert(String.equal name fname);
              {name;value=(get_struct_val_value value t)})
      in
      {v=Struct (strname, fields);t}
    end
  | _ -> get_sexp_value valu.full t

let get_vars tpref arg_name_gen =
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
    let arg_vars = List.foldi call.args ~init:known_vars
        ~f:(fun i acc arg ->
            let arg_type = get_fun_arg_type call.fun_name i in
            match arg.pointee with
            | Some ptee ->
              begin
                let ptee_type = get_pointee arg_type in
                assert(arg.is_ptr);
                let addr = (Sexp.to_string arg.value.full) in
                if ptee.is_fun_ptr then acc
                else begin
                  let value =
                    match ptee.before with
                    | Some v -> (get_struct_val_value v ptee_type)
                    | None ->
                      failwith ("arguments must be initialized for call " ^
                                call.fun_name)
                  in
                  alloc_local_arg addr value;
                  let before_vars =
                    match ptee.before with
                    | Some v -> get_vars_from_struct_val v ptee_type acc
                    | None -> acc in
                  match ptee.after with
                  | Some v -> get_vars_from_struct_val v ptee_type before_vars
                  | None -> before_vars
                end
              end
            | None ->
              assert(not arg.is_ptr);
              get_vars_from_struct_val arg.value arg_type acc)
    in
    let ret_vars = match call.ret with
      | Some ret -> get_vars_from_struct_val
                      ret.value (get_fun_ret_type call.fun_name) arg_vars
      (*TODO: get also ret.pointee vars.*)
      | None -> arg_vars in
    let add_vars_from_ctxt vars ctxt =
      map_set_n_update_alist vars (make_name_alist_from_var_decls
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

let rec render_assignment var =
  match var.value.v with
  | Struct (_, fvals) ->
    (*TODO: make sure that the var_value.t is also Str .*)
    String.concat ~sep:"\n"
      (List.map fvals
         ~f:(fun {name;value} -> render_assignment
                {name=(var.name ^ "." ^ name);value} ^ ";"))
  | Undef -> ""
  | _ -> var.name ^ " = " ^ (render_tterm var.value)

let render_vars_declarations ( vars : var_spec list ) =
  String.concat ~sep:"\n"
    (List.map vars ~f:(fun v ->
         match v.value.t with
         | Unknown | Sunknown | Uunknown ->
           "//" ^ ttype_to_str v.value.t ^ " " ^ v.name ^ ";"
         | _ ->
           ttype_to_str v.value.t ^ " " ^ v.name ^ ";")) ^ "\n"

let rec render_eq_sttmt ~is_assert out_arg (out_val:tterm) =
  let head = (if is_assert then "assert" else "assume") in
  match out_val.v with
  | Struct (_, fields) ->
    (*TODO: check that the types of Str (_,fts)
      are the same as in fields*)
    String.concat (List.map fields ~f:(fun {name;value} ->
      render_eq_sttmt ~is_assert (out_arg ^ "." ^ name) value))
  | _ -> "//@ " ^ head ^ "(" ^ out_arg ^ " == " ^
         (render_tterm out_val) ^ ");\n"

let render_fun_call_preamble call args =
  let pre_lemmas =
    match String.Map.find Fs.fun_types call.fun_name with
    | Some t -> (String.concat ~sep:"\n"
                   (List.map t.Fs.lemmas_before ~f:(fun l -> l args)))
    | None -> failwith "" in
  pre_lemmas ^ "\n"

let compose_fcall_preamble call args =
  match String.Map.find Fs.fun_types call.fun_name with
  | Some t -> (List.map t.Fs.lemmas_before ~f:(fun l -> l args))
  | None -> failwith ("function not found " ^ call.fun_name)


let extract_fun_args call =
  List.mapi call.args
    ~f:(fun i arg ->
        let a_type = get_fun_arg_type call.fun_name i in
        ( if arg.is_ptr then
            match arg.pointee with
            | Some ptee ->
              begin
                if ptee.is_fun_ptr then
                  match ptee.fun_name with
                  | Some n -> {v=Fptr n;t=a_type}
                  | None -> {v=Fptr "fun???";t=a_type}
                  else
                    let arg_name = String.Map.find !allocated_args
                        ( Sexp.to_string arg.value.full ) in
                    let ptee_t = match a_type with
                      | Ptr t -> t
                      | _ -> failwith ("inconsistent function argument for " ^
                                       call.fun_name)
                    in
                    match arg_name with
                    | Some n -> {v=Addr {v=(Id n.name);t=ptee_t};t=a_type}
                    | None -> {v=Addr {v=(Id "arg??");t=ptee_t};t=a_type}
              end
            | None -> {v=Undef;t=a_type}
          else
            get_struct_val_value arg.value a_type))

let find_false_eq_sttmts (sttmts:tterm list) =
  List.filter sttmts ~f:(fun sttmt ->
      match sttmt.v with
      | Bop (Eq,{v=Bool false;t=Boolean},_) -> true
      | _ -> false)

let find_complementary_sttmts sttmts1 sttmts2 =
  let find_from_left sttmts1 (sttmts2:tterm list) =
    List.find_map (find_false_eq_sttmts sttmts1) ~f:(fun sttmt1 ->
        match sttmt1.v with
        | Bop (_,_,rhs) ->
          List.find sttmts2 ~f:(fun sttmt2 -> term_eq rhs.v sttmt2.v)
        | _ -> None)
  in
  match find_from_left sttmts1 sttmts2 with
  | Some st -> Some (st,false)
  | None -> Option.map (find_from_left sttmts2 sttmts1)
              ~f:(fun rez -> (rez,true))

let compose_post_lemmas call ret_name args =
  let ret_name = match ret_name with
    | Some ret_name -> ret_name
    | None -> ""
  in
  match String.Map.find Fs.fun_types call.fun_name with
  | Some t -> List.map t.Fs.lemmas_after ~f:(fun l -> l ret_name args)
  | None -> failwith ("unknown function " ^ call.fun_name)

let render_post_statements call ~is_tip =
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
              render_eq_sttmt ~is_assert:is_tip
                out_arg.name (get_struct_val_value v out_arg.value.t)
            | None -> ""
          end
        | None -> ""
      else "") in
  let ret_post_asserts =
    (if is_tip then
       String.concat (List.map call.ret_context ~f:(fun sttmt ->
           "//@ assert(" ^ render_tterm (get_sexp_value sttmt Boolean) ^ ");\n"))
     else
       "") in
  (String.concat sttmts) ^ ret_post_asserts

let compose_args_post_conditions call =
  List.filter_map call.args ~f:(fun arg ->
      match arg.pointee with
      | Some ptee -> assert arg.is_ptr;
        begin
          match ptee.after with
          | Some v -> assert (not ptee.is_fun_ptr);
            let out_arg =
              let key =Sexp.to_string arg.value.full in
              match String.Map.find !allocated_args key with
              | Some out_arg -> out_arg
              | None -> failwith ("unknown argument " ^ key)
            in
            Some {name=out_arg.name;
                  value=(get_struct_val_value v out_arg.value.t)}
          | None -> assert ptee.is_fun_ptr;
            None
        end
      | None -> assert (not arg.is_ptr);
        None)

let extract_tip_ret_post_conditions call =
  List.map call.ret_context ~f:(fun sttmt ->
      get_sexp_value sttmt Boolean)

let render_fcall_preamble context =
  (String.concat ~sep:"\n" context.pre_lemmas) ^ "\n" ^
  (match context.ret_name with
   | Some name -> (ttype_to_str context.ret_type) ^
                  " " ^ name ^ " = "
   | None -> "") ^
  (render_term context.application) ^ ";\n" ^
  (String.concat ~sep:"\n" context.post_lemmas) ^ "\n"

let render_post_sttmts ~is_assert {args_post_conditions;
                                   ret_val=_;post_statements} =
  (String.concat ~sep:"\n" (List.map args_post_conditions
                              ~f:(fun {name;value} ->
                                  render_eq_sttmt ~is_assert
                                    name value))) ^ "\n" ^
  (String.concat ~sep:"\n" (List.map post_statements
                              ~f:(fun t ->
                                  "/*@ " ^ (if is_assert
                                            then "assert"
                                            else "assume") ^
                                  "(" ^ (render_tterm t) ^
                                  ");@*/")))

let render_ret_equ_sttmt ~is_assert ret_name ret_val =
  (match ret_name with
   | Some name -> (render_eq_sttmt ~is_assert name ret_val)
   | None -> "") ^ "\n"

let render_hist_fun_call {context;result} =
  (render_fcall_preamble context) ^
  render_post_sttmts ~is_assert:false result ^
  render_ret_equ_sttmt ~is_assert:false context.ret_name result.ret_val

let render_2tip_post_assertions res1 res2 ret_name =
  if term_eq res1.ret_val.v res2.ret_val.v then
    begin
      match find_complementary_sttmts
              res1.post_statements
              res2.post_statements with
      | Some (sttmt,fst) ->
        begin
          let res1_assertions =
            (render_post_sttmts ~is_assert:true res1 ^ "\n" ^
             render_ret_equ_sttmt ~is_assert:true ret_name res1.ret_val)
          in
          let res2_assertions =
            (render_post_sttmts~is_assert:true res2 ^ "\n" ^
             render_ret_equ_sttmt ~is_assert:true ret_name res2.ret_val)
          in
          let (pos_sttmts,neg_sttmts) =
            if fst then
              res1_assertions,res2_assertions
            else
              res2_assertions,res1_assertions
          in
          "if (" ^ (render_tterm sttmt) ^ ") {\n" ^
          pos_sttmts ^ "} else {\n" ^
          neg_sttmts ^ "}\n"
        end
      | None -> failwith "Tip calls non-differentiated by ret, nor \
                          by a complementary post-conditions are \
                          not supported"
    end
  else
    let rname = match ret_name with
      | Some n -> n
      | None -> failwith "this can't be true!"
    in
    "if (" ^ rname ^ " == " ^ (render_tterm res1.ret_val) ^ ") {\n" ^
    (render_post_sttmts ~is_assert:true res1) ^ "} else {\n" ^
    (render_post_sttmts ~is_assert:true res2) ^ "\n" ^
    (render_ret_equ_sttmt ~is_assert:true ret_name res2.ret_val) ^ "}\n"

let render_export_point name =
  "int " ^ name ^ ";\n"

let render_tip_fun_calls {context;results} export_point =
  (render_fcall_preamble context) ^
  (render_export_point export_point) ^
  (match results with
   | result :: [] ->
     (render_post_sttmts ~is_assert:true result) ^ "\n" ^
     (render_ret_equ_sttmt ~is_assert:true context.ret_name result.ret_val)
   | res1 :: res2 :: [] ->
     render_2tip_post_assertions res1 res2 context.ret_name
   | [] -> failwith "must be at least one tip call"
   | _ -> failwith "more than two outcomes are not supported.") ^ "\n"

let get_ret_val call =
  match call.ret with
  | Some ret ->
    let t = get_fun_ret_type call.fun_name in
    get_struct_val_value ret.value t
  | None -> {v=Undef;t=Unknown}

let extract_common_call_context call (ret_name:string option) args =
  let ret_type = get_fun_ret_type call.fun_name in
  let arg_names = List.map args ~f:render_tterm in
  let pre_lemmas = compose_fcall_preamble call arg_names in
  let application = Apply (call.fun_name,args) in
  let post_lemmas = compose_post_lemmas call ret_name arg_names in
  {pre_lemmas;application;post_lemmas;ret_name;ret_type}

let extract_hist_call_context call rname_gen =
  let ret_name = if is_void (get_fun_ret_type call.fun_name) then None
    else Some rname_gen#generate in
  let args = extract_fun_args call in
  let args_post_conditions = compose_args_post_conditions call in
  {context=extract_common_call_context call ret_name args;
   result={args_post_conditions;ret_val=get_ret_val call;
           post_statements=[]}}

let tip_calls_context calls rname_gen =
  let call = List.hd_exn calls in
  let ret_name = if is_void (get_fun_ret_type call.fun_name) then None
    else Some rname_gen#generate in
  let args = extract_fun_args call in
  let context = extract_common_call_context call ret_name args in
  let results = List.map calls ~f:(fun call ->
      let args_post_conditions = compose_args_post_conditions call in
      {args_post_conditions;
       ret_val=get_ret_val call;
       post_statements=(extract_tip_ret_post_conditions call);})
  in
  {context;results}

let render_hist_calls hist_funs =
  String.concat ~sep:"\n" (List.map hist_funs ~f:render_hist_fun_call)

let extract_calls_info tpref =
  let rez_gen = name_gen "rez" in
  let hist_funs =
    (List.map tpref.history ~f:(fun call ->
         extract_hist_call_context call rez_gen))
  in
  let tip_calls = tip_calls_context tpref.tip_calls rez_gen in
  hist_funs, tip_calls

let render_cmplexes cmplxes =
  String.concat ~sep:"\n" (List.map (String.Map.data cmplxes) ~f:(fun var ->
      (ttype_to_str var.value.t) ^ " " ^ var.name ^ ";//" ^
      (render_tterm var.value))) ^ "\n"

let render_tmps tmps =
  String.concat ~sep:"\n" (List.map (List.sort ~cmp:(fun a b ->
      (String.compare a.name b.name))
      (String.Map.data tmps))
      ~f:(fun tmp ->
          ttype_to_str tmp.value.t ^ " " ^ tmp.name ^ " = " ^
          render_tterm tmp.value ^ ";")) ^ "\n"

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

let render_context_assumptions assumptions  =
  String.concat ~sep:"\n" (List.map assumptions ~f:(fun t ->
    "//@ assume(" ^ (render_tterm t) ^ ");")) ^ "\n"

let rec get_relevant_segment pref =
  match List.findi pref.history ~f:(fun _ call ->
      String.equal call.fun_name "loop_invariant_consume") with
  | Some (pos,_) ->
    let tail_len = (List.length pref.history) - pos - 1 in
    get_relevant_segment
      {history = List.sub pref.history ~pos:(pos + 1) ~len:tail_len;
       tip_calls = pref.tip_calls;}
  | None -> pref

let render_leaks leaks =
  String.concat ~sep:"\n" leaks ^ "\n"

let extract_leaks ccontexts =
  let leak_map =
    List.fold ccontexts ~init:String.Map.empty ~f:(fun acc {ret_name;application;_} ->
        match application with
        | Apply (fname,args) ->
          let args = List.map args ~f:render_tterm in
          let spec = String.Map.find_exn Fs.fun_types fname in
          let ret_name = match ret_name with Some name -> name | None -> "" in
          List.fold spec.Fs.leaks ~init:acc ~f:(fun acc l ->
              l ret_name args acc)
        | _ -> failwith "call context applicatio must be Apply")
  in
  String.Map.data leak_map

let render_allocated_args args =
  String.concat ~sep:"\n"
    (List.map (String.Map.data args)
       ~f:(fun spec -> (ttype_to_str spec.value.t) ^ " " ^
                       (spec.name) ^ ";")) ^ "\n"

let render_alloc_args_assignments () =
  String.concat ~sep:"\n"
    (List.map (String.Map.data !allocated_args) ~f:(fun arg ->
       render_assignment arg ^ ";"))

let render_args_assignments args =
  String.concat ~sep:"\n"
    (List.map (String.Map.data args) ~f:(fun arg ->
       render_assignment arg ^ ";"))

let build_ir fin =
  let pref = get_relevant_segment
      (Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin)) in
  let preamble = preamble ^
                 "void to_verify()\
                  /*@ requires true; @*/ \
                  /*@ ensures true; @*/\n{\n" in
  let export_point = "export_point" in
  let free_vars = (get_vars pref (name_gen "arg")) in
  let (hist_calls,tip_call) = extract_calls_info pref in
  let leaks = extract_leaks
      ((List.map hist_calls ~f:(fun hc -> hc.context))@[tip_call.context]) in
  let cmplxs = !allocated_complex_vals in
  let tmps = !allocated_tmp_vals in
  let context_assumptions = collect_context pref in
  let arguments = !allocated_args in
  {preamble;free_vars;arguments;tmps;
   cmplxs;context_assumptions;hist_calls;tip_call;
   leaks;export_point}

let prepare_tasks ir =
  List.map ir.tip_call.results ~f:(fun result ->
      let exists_such =
        (List.map result.args_post_conditions
           ~f:(fun spec -> {v=Bop (Eq,{v=Id spec.name;t=Unknown},
                                   spec.value);
                            t=Boolean})) @
        result.post_statements
      in
      let exists_such =
        match ir.tip_call.context.ret_name with
        | Some ret_name ->
          {v=Bop (Eq,{v=Id ret_name;t=ir.tip_call.context.ret_type},
                  result.ret_val);t=Boolean} :: exists_such
        | None -> exists_such
      in
      {exists_such;
       filename="aaa.c";
       export_point=ir.export_point})

let convert_prefix fin cout =
  let ir = build_ir fin in
  Out_channel.output_string cout ir.preamble;
  Out_channel.output_string cout (render_cmplexes ir.cmplxs);
  Out_channel.output_string cout (render_vars_declarations (String.Map.data ir.free_vars));
  Out_channel.output_string cout (render_allocated_args ir.arguments);
  Out_channel.output_string cout (render_context_assumptions ir.context_assumptions);
  Out_channel.output_string cout (render_tmps ir.tmps);
  Out_channel.output_string cout (render_args_assignments ir.arguments);
  Out_channel.output_string cout (render_hist_calls ir.hist_calls);
  Out_channel.output_string cout (render_tip_fun_calls ir.tip_call ir.export_point);
  Out_channel.output_string cout (render_leaks ir.leaks);
  Out_channel.output_string cout "}\n";
  Out_channel.with_file "tasks.sexp" ~f:(fun fout ->
      Out_channel.output_string fout
        (Sexp.to_string (List.sexp_of_t Ir.sexp_of_task (prepare_tasks ir))))

let () =
  Out_channel.with_file Sys.argv.(2) ~f:(fun fout ->
      convert_prefix Sys.argv.(1) fout)
