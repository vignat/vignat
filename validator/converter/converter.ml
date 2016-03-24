open Core.Std
open Trace_prefix
open Ir

module Fs = Function_spec

let preamble = In_channel.read_all "preamble.tmpl"


let allocated_args : var_spec String.Map.t ref = ref String.Map.empty

let infer_signed_type w =
  if String.equal w "w32" then Sint32
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
  let t_final = match spec.v.t with
    | Unknown -> v.t
    | Sunknown | Uunknown -> if v.t = Unknown then spec.v.t else v.t
    | _ -> spec.v.t in
  let v_final = match spec.v.v with
    | Undef -> v.v
    | _ -> spec.v.v in
  {name = spec.name;
   v = {v=v_final; t=t_final};}

let rec get_var_decls_of_sexp exp t known_vars =
  match get_var_name_of_sexp exp, get_read_width_of_sexp exp with
  | Some name, Some w ->
    begin match String.Map.find known_vars name with
      | Some spec -> [update_var_spec spec {v=Undef;t=(determine_type t w)}]
      | None -> [{name = name; v={v=Undef;t=determine_type t w}}]
    end
  | None, None ->
    begin
    match exp with
    | Sexp.List (Sexp.Atom f :: Sexp.Atom w :: tl)
      when (String.equal w "w32") || (String.equal w "w16") || (String.equal w "w8") ->
      let ty = determine_type (infer_type_class f) w in
      (List.join (List.map tl ~f:(fun e -> get_var_decls_of_sexp e ty known_vars)))
    | Sexp.List (Sexp.Atom f :: tl) ->
      let ty = match (infer_type_class f) with
        | Unknown -> begin match guess_type_l tl with
            | Unknown -> t
            | ty -> ty
          end
        | tc -> tc
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
let allocated_complex_vals = ref String.Map.empty

let tmp_val_name_gen = name_gen "tmp"
let allocated_tmp_vals = ref []

let get_sint_in_bounds v =
  let integer_val = Int.of_string v in
  if Int.(integer_val > 2147483647) then
    integer_val - 2*2147483648
  else
    integer_val

let make_cmplx_val exp t =
  let key = Sexp.to_string exp in
  match String.Map.find !allocated_complex_vals key with
  | Some v -> v.v
  | None ->
    let name = complex_val_name_gen#generate in
    let value = {v=Id name;t} in
    allocated_complex_vals :=
      String.Map.add !allocated_complex_vals ~key
        ~data:{name = name;
               v=value;};
    value

let allocate_tmp value =
  let name = tmp_val_name_gen#generate in
  allocated_tmp_vals :=
    {name = name; v=value} :: !allocated_tmp_vals;
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

let strip_outside_parens str =
  if (String.is_prefix str ~prefix:"(") &&
     (String.is_suffix str ~suffix:")") then
    String.chop_prefix_exn (String.chop_suffix_exn str ~suffix:")")
      ~prefix:"("
  else str

let rec get_sexp_value exp t =
  let exp = expand_shorted_sexp exp in
  let exp = eliminate_false_eq_0 exp t in
  match exp with
  | Sexp.Atom v ->
    begin
      match t with
      | Sint32 -> {v=Int (get_sint_in_bounds v);t}
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
          ~f:(fun {fname;value} (name,t) -> (*How did it allow two name args?*)
              assert(String.equal fname name);
              (name,(get_struct_val_value value t)))
      in
      {v=Struct (strname, fields);t}
      (*failwith ("Inline structure values not supported. " ^
                        (Sexp.to_string valu.full))*)
    end
  | _ -> get_sexp_value valu.full t

let get_vars tpref arg_name_gen =
  let get_vars known_vars call =
    let alloc_local_arg addr v =
      match String.Map.find !allocated_args addr with
      | None ->
        let p_name = arg_name_gen#generate in
        allocated_args := String.Map.add !allocated_args
            ~key:addr ~data:{name = p_name;
                             v};
      | Some spec ->
        allocated_args := String.Map.add !allocated_args
            ~key:addr ~data:(update_var_spec spec v)
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

let render_bop = function
  | Eq -> "=="
  | Le -> "<="
  | Lt -> "<"
  | Ge -> ">="
  | Gt -> ">"
  | Add -> "+"
  | Sub -> "-"
  | And -> "&&"

let rec render_tterm (t:tterm) =
  match t.v with  (*strip parens: account for weird VeriFast parser*)
  | Bop (op, lhs, rhs) -> "(" ^ (strip_outside_parens (render_tterm lhs)) ^
                          " " ^ (render_bop op) ^ " " ^
                          (render_tterm rhs) ^ ")"
  | Apply (_,args) ->
    let arg_strings = List.map args ~f:render_tterm in
    "fname(" ^ (String.concat ~sep:", " arg_strings) ^ ")"
  | Id name -> name;
  | Struct (_,fields) ->
    "{" ^ (String.concat ~sep:", "
             (List.map fields ~f:(fun (name,value) ->
                  name ^ " = " ^ (render_tterm value)))) ^
    "}"
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Not t -> "!(" ^ (render_tterm t) ^ ")"
  | Str_idx (t,field_name) -> "(" ^ (render_tterm t) ^ ")." ^ field_name
  | Deref t -> "*(" ^ (render_tterm t) ^ ")"
  | Fptr f -> f
  | Addr t -> "&(" ^ (render_tterm t) ^ ")"
  | Cast (t,v) -> "(" ^ ttype_to_str t ^ ")" ^ (render_tterm v)
  | Undef -> "???"

let rec render_assignment var_name (var_value:tterm) =
  match var_value.v with
  | Struct (_, fvals) ->
    (*TODO: make sure that the var_value.t is also Str .*)
    String.concat ~sep:"\n"
      (List.map fvals
         ~f:(fun (name,value) -> render_assignment
                (var_name ^ "." ^ name) value ^ ";"))
  | Undef -> ""
  | _ -> var_name ^ " = " ^ (render_tterm var_value)

let render_vars_declarations ( vars : var_spec list ) =
  String.concat ~sep:"\n"
    (List.map vars ~f:(fun v ->
         match v.v.t with
         | Unknown | Sunknown | Uunknown ->
           "//" ^ ttype_to_str v.v.t ^ " " ^ v.name ^ ";"
         | _ ->
           ttype_to_str v.v.t ^ " " ^ v.name ^ ";"))

let render_var_assignments ( vars : var_spec list ) =
  String.concat ~sep:"\n"
    (List.map vars ~f:(fun v ->
       render_assignment v.name v.v))

let rec render_eq_sttmt ~is_assert out_arg (out_val:tterm) =
  let head = (if is_assert then "assert" else "assume") in
  match out_val.v with
  | Struct (_, fields) ->
    (*TODO: check that the types of Str (_,fts)
      are the same as in fields*)
    String.concat (List.map fields ~f:(fun (name,value) ->
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

let gen_fun_call_arg_list call =
  List.mapi call.args
      ~f:(fun i arg ->
          let a_type = get_fun_arg_type call.fun_name i in
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
              render_tterm (get_struct_val_value arg.value a_type)))

let render_fun_call call ret_var args ~is_tip =
  let arg_list = String.concat ~sep:", " args in
  let fname_with_args = String.concat [call.fun_name; "("; arg_list; ");\n"] in
  let call_with_ret call_body = match call.ret with
    | Some ret ->
      begin
        let t = get_fun_ret_type call.fun_name in
        let ret_val = get_struct_val_value ret.value t in
        let ret_ass = render_eq_sttmt ~is_assert:is_tip ret_var ret_val in
        ttype_to_str t ^ " " ^ ret_var ^ " = " ^ call_body ^ ret_ass
      end
    | None -> call_body
  in
  call_with_ret (fname_with_args)

let find_false_eq_sttmts sttmts =
  List.filter sttmts ~f:(fun sttmt ->
      match sttmt with
      | Sexp.List [Sexp.Atom rel; Sexp.Atom lhs; _] ->
        (String.equal rel "Eq") && (String.equal lhs "false")
      | _ -> false)

let find_complementary_sttmts sttmts1 sttmts2 =
  let find_from_left sttmts1 sttmts2 =
  List.find_map (find_false_eq_sttmts sttmts1) ~f:(fun sttmt1 ->
      match sttmt1 with
      | Sexp.List [Sexp.Atom rel; Sexp.Atom lhs; rhs]
        when (String.equal rel "Eq") && (String.equal lhs "false") ->
        List.find sttmts2 ~f:(Sexp.equal rhs)
      | _ -> None)
  in
  match find_from_left sttmts1 sttmts2 with
  | Some st -> Some st
  | None -> find_from_left sttmts2 sttmts1

let render_2tip_call fst_tip snd_tip ret_var args =
  let arg_list = String.concat ~sep:", " args in
  let fname_with_args = String.concat [fst_tip.fun_name; "("; arg_list; ");\n"] in
  let call_with_ret call_body = match fst_tip.ret with
    | Some _ ->
      begin
        match snd_tip.ret with
        | Some _ ->
          let t = get_fun_ret_type fst_tip.fun_name in
          ttype_to_str t ^ " " ^ ret_var ^ " = " ^ call_body
        | None -> failwith "tip call must either allways return or never"
      end
    | None -> call_body
  in
  call_with_ret (fname_with_args)

let render_post_lemmas call ret_name args =
  let post_lemmas =
    match String.Map.find Fs.fun_types call.fun_name with
    | Some t -> (String.concat ~sep:"\n"
                   (List.map t.Fs.lemmas_after ~f:(fun l -> l ret_name args)))
    | None -> failwith "" in
  post_lemmas

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
                out_arg.name (get_struct_val_value v out_arg.v.t)
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

let render_fun_call_fabule call ret_name args ~is_tip =
  let post_statements = render_post_statements call ~is_tip in
  (render_post_lemmas call ret_name args) ^ "\n" ^ post_statements

let rec term_eq a b =
  match a,b with
  | Bop (opa,lhsa,rhsa), Bop (opb,lhsb,rhsb) ->
    opa = opb && (term_eq lhsa.v lhsb.v) && (term_eq rhsa.v rhsb.v)
  | Apply (fa,argsa), Apply (fb, argsb) ->
    (String.equal fa fb) && ((List.length argsa) = (List.length argsb)) &&
    (List.for_all2_exn argsa argsb ~f:(fun arga argb -> term_eq arga.v argb.v))
  | Id a, Id b -> String.equal a b
  | Struct (sna,fdsa), Struct (snb,fdsb) ->
    (String.equal sna snb) && ((List.length fdsa) = (List.length fdsb)) &&
    (List.for_all2_exn fdsa fdsb ~f:(fun (fnamea,fvala) (fnameb,fvalb) ->
         (String.equal fnamea fnameb) &&
         term_eq fvala.v fvalb.v))
  | Int ia, Int ib -> ia = ib
  | Bool ba, Bool bb -> ba = bb
  | Not tta, Not ttb -> term_eq tta.v ttb.v
  | Str_idx (tta,fda), Str_idx (ttb,fdb) -> term_eq tta.v ttb.v && String.equal fda fdb
  | Deref tta, Deref ttb -> term_eq tta.v ttb.v
  | Fptr fa, Fptr fb -> String.equal fa fb
  | Addr tta, Addr ttb -> term_eq tta.v ttb.v
  | Cast (ctypea,terma), Cast (ctypeb,termb) -> (ctypea = ctypeb) && (term_eq terma.v termb.v)
  | Undef, Undef -> true
  | _, _ -> false

let render_2tip_call_fabule fst_tip snd_tip ret_name args =
  let post_statements_fst_alternative = render_post_statements fst_tip ~is_tip:true in
  let post_statements_snd_alternative = render_post_statements snd_tip ~is_tip:true in
  let ret_t = get_fun_ret_type fst_tip.fun_name in
  match fst_tip.ret, snd_tip.ret with
  | Some r1, Some r2
    when not (term_eq (get_struct_val_value r1.value ret_t).v
                (get_struct_val_value r2.value ret_t).v) ->
    (render_post_lemmas fst_tip ret_name args) ^ "\n" ^
    "if (" ^ ret_name ^ " == " ^
    (render_tterm (get_struct_val_value r1.value ret_t) ^ ") {\n" ^
     post_statements_fst_alternative ^
     "\n} else {\n" ^
     (render_eq_sttmt ~is_assert:true ret_name
        (get_struct_val_value r2.value ret_t)) ^ "\n" ^
     post_statements_snd_alternative ^ "\n}\n")
  | Some _, Some _ -> begin match find_complementary_sttmts
                                      fst_tip.ret_context
                                      snd_tip.ret_context with
      | Some sttmt ->
        let pos_sttmts,neg_sttmts =
          (if List.mem fst_tip.ret_context sttmt then
             post_statements_fst_alternative,
             post_statements_snd_alternative
           else post_statements_snd_alternative,
                post_statements_fst_alternative)
        in
        "if (" ^ (render_tterm (get_sexp_value sttmt Boolean)) ^ ") {\n" ^
        pos_sttmts ^ "} else {\n" ^
        neg_sttmts ^ "}\n"
      | None -> failwith "tip calls non-differentiated by ret nor\
                          by a complementary condition are not supported"
    end
  | _,_ -> failwith "tip calls non-differentiated by return value not supported."

let render_fun_call_in_context call rname_gen =
  let ret_name = (if is_void (get_fun_ret_type call.fun_name) then ""
                 else rname_gen#generate) in
  let args = (gen_fun_call_arg_list call) in
  (render_fun_call_preamble call args) ^
  (render_fun_call call ret_name args ~is_tip:false) ^
  (render_fun_call_fabule call ret_name args ~is_tip:false)

let render_tip_call_in_context calls rname_gen =
  if List.length calls = 1 then
    let call = List.hd_exn calls in
    let ret_name = (if is_void (get_fun_ret_type call.fun_name) then ""
                    else rname_gen#generate) in
    let args = (gen_fun_call_arg_list call) in
    (render_fun_call_preamble call args) ^
    (render_fun_call call ret_name args ~is_tip:true) ^
    (render_fun_call_fabule call ret_name args ~is_tip:true)
  else if List.length calls = 2 then
    let fst_tip = List.hd_exn calls in
    let snd_tip = List.nth_exn calls 1 in
    let ret_name = rname_gen#generate in
    let args = (gen_fun_call_arg_list fst_tip) in
    (*TODO: assert that the inputs of the tip calls are identicall.*)
    (render_fun_call_preamble fst_tip args) ^
    (render_2tip_call fst_tip snd_tip ret_name args) ^
    (render_2tip_call_fabule fst_tip snd_tip ret_name args)
  else failwith "0 or too many tip-calls"

let render_function_list tpref =
  let rez_gen = name_gen "rez" in
  let hist_funs =
    (List.fold_left tpref.history ~init:""
       ~f:(fun str_acc call ->
           str_acc ^ render_fun_call_in_context call rez_gen))
  in
  let tip_call =
    (render_tip_call_in_context tpref.tip_calls rez_gen) in
  hist_funs ^ tip_call

let render_cmplxes () =
  String.concat (List.map (String.Map.data !allocated_complex_vals) ~f:(fun var ->
      ((ttype_to_str var.v.t) ^ " " ^ var.name ^ ";//") ^
      (render_tterm var.v) ^ "\n"))

let render_tmps () =
  String.concat (List.map (List.rev !allocated_tmp_vals) ~f:(fun var ->
      ((ttype_to_str var.v.t) ^ " " ^ var.name ^ " = ") ^
      (render_tterm var.v) ^ ";\n"))

let render_context pref =
  let render_ctxt_list l =
    String.concat ~sep:"\n" (List.map l ~f:(fun e ->
        "//@ assume(" ^ (render_tterm (get_sexp_value e Boolean)) ^ ");"))
  in
  (String.concat ~sep:"\n" (List.map pref.history ~f:(fun call ->
       (render_ctxt_list call.call_context) ^ "\n" ^
       (render_ctxt_list call.ret_context)))) ^ "\n" ^
  (match pref.tip_calls with
   | hd :: _ -> (render_ctxt_list hd.call_context) ^ "\n"
   | [] -> failwith "must have at least one tip call")

let rec get_relevant_segment pref =
  match List.findi pref.history ~f:(fun _ call ->
      String.equal call.fun_name "loop_invariant_consume") with
  | Some (pos,_) ->
    let tail_len = (List.length pref.history) - pos - 1 in
    get_relevant_segment
      {history = List.sub pref.history ~pos:(pos + 1) ~len:tail_len;
       tip_calls = pref.tip_calls;}
  | None -> pref

let render_leaks pref =
  ( String.concat ~sep:"\n" (List.map ( (List.hd_exn pref.tip_calls)::pref.history ) ~f:(fun call ->
      match String.Map.find Fs.fun_types call.fun_name with
      | Some t -> String.concat ~sep:"\n" t.Fs.leaks
      | None -> failwith "unknown function") ) ^ "\n")

let render_allocated_args () =
  ( String.concat ~sep:"\n" (List.map (String.Map.data !allocated_args)
                               ~f:(fun spec -> (ttype_to_str spec.v.t) ^ " " ^
                                               (spec.name) ^ ";")))

let render_alloc_args_assignments () =
  String.concat ~sep:"\n"
    (List.map (String.Map.data !allocated_args) ~f:(fun arg ->
       render_assignment arg.name arg.v ^ ";"))

let convert_prefix fin cout =
  Out_channel.output_string cout preamble ;
  Out_channel.output_string cout "void to_verify()\
                                  /*@ requires true; @*/ \
                                  /*@ ensures true; @*/\n{\n" ;
  let pref = get_relevant_segment
      (Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin)) in
  let vars = (get_vars pref (name_gen "arg")) in
  let vars_list = String.Map.data vars in
  let var_decls = (render_vars_declarations vars_list) in
  let fun_calls = (render_function_list pref) in
  let var_assigns = (render_var_assignments vars_list) in
  let leaks = (render_leaks pref) in
  let context_lemmas = ( render_context pref ) in
  let args_assignments = ( render_alloc_args_assignments ()) in
  Out_channel.output_string cout ( render_cmplxes () );
  Out_channel.output_string cout var_decls;
  Out_channel.output_string cout context_lemmas;
  Out_channel.output_string cout ( render_tmps ());
  Out_channel.output_string cout ( render_allocated_args ());
  Out_channel.newline cout;
  Out_channel.output_string cout args_assignments;
  Out_channel.output_string cout var_assigns;
  Out_channel.output_string cout fun_calls;
  Out_channel.output_string cout leaks;
  Out_channel.output_string cout "}\n"

let () =
  Out_channel.with_file Sys.argv.(2) ~f:(fun fout ->
      convert_prefix Sys.argv.(1) fout)
