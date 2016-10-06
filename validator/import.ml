open Core.Std
open Trace_prefix
open Ir
open Fspec_api

type 'x confidence = Sure of 'x | Tentative of 'x | Noidea

type t_width = W1 | W8 | W16 | W32
type t_sign = Sgn | Unsgn
type type_guess = {w:t_width confidence;
                   s:t_sign confidence;
                   precise: ttype}

type typed_var = {vname:string; t: type_guess;}

type address_spec = {value:tterm; callid:int; str_depth:int}

let known_addresses : address_spec list Int64.Map.t ref = ref Int64.Map.empty

let infer_signed_type w =
  if String.equal w "w32" then Sint32
  else if String.equal w "w8" then Sint8
  else Sunknown
  (* TODO: this computation sometimes is not necessary,
     so this exception may break a problem free insuction.
     else failwith (w ^ " signed is not supported")*)

let infer_unsigned_type w =
  if String.equal w "w32" then Uint32
  else if String.equal w "w16" then Uint16
  else if String.equal w "w8" then Uint8
  else failwith (w ^ " unsigned is not supported")

let infer_type_sign f =
  if String.equal f "Sle" then Sure Sgn
  else if String.equal f "Slt" then Sure Sgn
  else if String.equal f "Ule" then Sure Unsgn
  else if String.equal f "Ult" then Sure Unsgn
  else Noidea

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

let map_set_n_update_alist mp lst =
  List.fold lst ~init:mp ~f:(fun acc (key,data) ->
      String.Map.add acc ~key ~data)

let is_int str =
  (* As a hack: handle -10 in 64bits.
     TODO: handle more generally*)
  if (String.equal str "18446744073709551606") then true
  else
    try ignore (int_of_string str); true
    with _ -> false

let guess_sign exp known_vars =
  match get_var_name_of_sexp exp with
  | Some v -> begin match String.Map.find known_vars v with
      | Some spec -> spec.t.s
      | None -> Noidea
    end
  | None -> match exp with
    | Sexp.Atom x -> if is_int x then Tentative Unsgn
      else Noidea
    | _ -> Noidea

let rec guess_sign_l exps known_vars =
  match exps with
  | hd :: tl -> begin match guess_sign hd known_vars with
      | Noidea -> guess_sign_l tl known_vars
      | s -> s
    end
  | [] -> Noidea

let update_tterm (known:tterm) (given:tterm) =
  let t_final = match known.t with
    | Unknown -> given.t
    | Sunknown | Uunknown -> if given.t = Unknown then known.t else given.t
    | _ -> known.t in
  let v_final = match known.v with
    | Undef -> given.v
    | _ -> known.v in
  {t=t_final;v=v_final}

let choose_guess g1 g2 =
  match g1,g2 with
  | Noidea, _ -> g2
  | Sure _, _ -> g1
  | Tentative _, Sure _ -> g2
  | Tentative _, _ -> g1

let update_ttype (known:type_guess) given =
  match known.precise,given.precise with
  | Unknown,Unknown ->
    let w = choose_guess known.w given.w in
    let s = choose_guess known.s given.s in
    {precise=Unknown;w;s}
  | Unknown,_ -> given
  | _,Unknown -> known
  | _,_ -> known


let update_var_spec (spec:typed_var) t =
  {vname = spec.vname;
   t = (update_ttype spec.t t);}

let failback_type t1 t2 =
  match t1 with
  | Unknown -> t2
  | _ -> t1

let convert_str_to_width_confidence w =
  if String.equal w "w1" then Sure W1
  else if String.equal w "w8" then Sure W8
  else if String.equal w "w16" then Sure W16
  else if String.equal w "w32" then Sure W32
  else Noidea

let is_bool_fun fname =
  if String.equal fname "Eq" then true
  else if String.equal fname "Sle" then true
  else if String.equal fname "Slt" then true
  else if String.equal fname "Ule" then true
  else if String.equal fname "Ult" then true
  else false

let sign_to_str s =
  match s with
  | Noidea -> "??"
  | Tentative Sgn -> "-?"
  | Sure Sgn -> "-!"
  | Tentative Unsgn -> "+?"
  | Sure Unsgn -> "+!"

let rec get_var_decls_of_sexp exp {s;w=_;precise} (known_vars:typed_var String.Map.t) : typed_var list =
  match get_var_name_of_sexp exp, get_read_width_of_sexp exp with
  | Some name, Some w ->
    begin match String.Map.find known_vars name with
      | Some spec -> [update_var_spec spec {precise;s;w=convert_str_to_width_confidence w}]
      | None -> [{vname = name; t={precise;s;w=convert_str_to_width_confidence w}}]
    end
  | None, None ->
    begin
    match exp with
    | Sexp.List [Sexp.Atom f; lhs; rhs]
      when is_bool_fun f->
      let s = choose_guess (infer_type_sign f) (guess_sign_l [lhs;rhs] known_vars) in
      (get_var_decls_of_sexp lhs {s;w=Noidea;precise=Unknown;} known_vars) @
      (get_var_decls_of_sexp rhs {s;w=Noidea;precise=Unknown;} known_vars)
    | Sexp.List (Sexp.Atom f :: Sexp.Atom w :: tl)
      when (String.equal w "w32") || (String.equal w "w16") || (String.equal w "w8") ->
      if String.equal f "ZExt" then
        match tl with
        | [tl] -> get_var_decls_of_sexp
                    tl {s=(Sure Unsgn);w=Noidea;precise=Unknown} known_vars
        | _ -> failwith "ZExt may have only one argument (besides w..)."
      else
        let si = choose_guess (infer_type_sign f) s in
        (List.join (List.map tl ~f:(fun e ->
             get_var_decls_of_sexp e {s=si;w=Noidea;precise} known_vars)))
    | Sexp.List (Sexp.Atom f :: tl) ->
      let si = choose_guess (infer_type_sign f)
          (choose_guess (guess_sign_l tl known_vars) s)
      in
      List.join (List.map tl ~f:(fun e -> get_var_decls_of_sexp e {s=si;w=Noidea;precise} known_vars))
    | _ -> []
    end
  | _,_ -> failwith "inconsistency in get_var_name/get_read_width"

let make_name_alist_from_var_decls (lst: typed_var list) =
  List.map lst ~f:(fun x -> (x.vname,x))

let get_vars_from_plain_val v type_guess known_vars =
  (*TODO: proper type induction here, e.g. Sadd w16 -> Sint16, ....*)
  let decls = get_var_decls_of_sexp v type_guess known_vars in
  map_set_n_update_alist known_vars (make_name_alist_from_var_decls decls)

let type_guess_of_ttype t = match t with
  | Sint32 -> {s=Sure Sgn;w=Sure W32;precise=t}
  | Sint8 -> {s=Sure Sgn;w=Sure W8;precise=t}
  | Uint32 -> {s=Sure Unsgn;w=Sure W32;precise=t}
  | Uint16 -> {s=Sure Unsgn;w=Sure W16;precise=t}
  | Uint8 -> {s=Sure Unsgn;w=Sure W8;precise=t}
  | Sunknown -> {s=Sure Sgn;w=Noidea;precise=Unknown}
  | Uunknown -> {s=Sure Unsgn;w=Noidea;precise=Unknown}
  | Unknown | _ -> {s=Noidea;w=Noidea;precise=t}

let rec get_vars_from_struct_val v (ty:ttype) (known_vars:typed_var String.Map.t) =
  match ty with
  | Str (name, fields) ->
    let ftypes = List.map fields ~f:snd in
    if (List.length v.break_down) <>
       (List.length fields)
    then
      failwith ("Mismatch between expected (" ^
                (Int.to_string (List.length fields)) ^
                ") and traced (" ^
                (Int.to_string (List.length v.break_down)) ^
                ") breakdowns for " ^
                name ^ ".")
    else
      List.fold (List.zip_exn v.break_down ftypes) ~init:known_vars
        ~f:(fun acc (v,t)->
          get_vars_from_struct_val v.value t acc)
  | ty -> match v.full with
    | Some v ->
      get_vars_from_plain_val v (type_guess_of_ttype ty) known_vars
    | None -> known_vars

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
  (*Special case for 64bit -1, for now,
    FIXME: make a more general case.*)
  if (String.equal v "18446744073709551606") then -10
  else
    let integer_val = Int.of_string v in
    if Int.(integer_val > 2147483647) then
      integer_val - 2*2147483648
    else
      integer_val

let make_cmplx_val exp t =
  let key = Sexp.to_string exp in
  match String.Map.find !allocated_complex_vals key with
  | Some spec -> {v=Id spec.name;t=spec.value.t}
  | None ->
    let name = complex_val_name_gen#generate in
    let value = {v=Id key;t} in
    allocated_complex_vals :=
      String.Map.add !allocated_complex_vals ~key
        ~data:{name;value};
    {v=Id name;t}

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

let rec is_bool_expr exp =
  match exp with
  | Sexp.List [Sexp.Atom f; _; _] when is_bool_fun f -> true
  | Sexp.List [Sexp.Atom a; _; lhs; rhs] when String.equal a "And" ->
    (*FIXME: and here, but really that is a bool expression, I know it*)
    (is_bool_expr lhs) || (is_bool_expr rhs)
  | Sexp.List [Sexp.Atom ext; _; e] when String.equal ext "ZExt" ->
    is_bool_expr e
  | _ -> false

(* TODO: elaborate. *)
let guess_type _ = Unknown

let rec guess_type_l exps =
  match exps with
  | hd :: tl -> begin match guess_type hd with
      | Unknown -> guess_type_l tl
      | s -> s
    end
  | [] -> Unknown

let rec get_sexp_value exp t =
  let exp = expand_shorted_sexp exp in
  let exp = eliminate_false_eq_0 exp t in
  match exp with
  | Sexp.Atom v ->
    begin
      let t = match t with
        |Unknown|Sunknown|Uunknown -> guess_type exp
        |_ -> t
      in
      match t with
      | Sint32 -> {v=Int (get_sint_in_bounds v);t}
      | _ ->
        if String.equal v "true" then {v=Bool true;t=Boolean}
        else if String.equal v "false" then {v=Bool false;t=Boolean}
        (*FIXME: deduce the true integer type for the value: *)
        else if is_int v then {v=Int (int_of_string v);t}
        else {v=Id v;t}
    end
  | Sexp.List [Sexp.Atom f; Sexp.Atom w; Sexp.Atom offset; src;]
    when (String.equal f "Extract") && (String.equal offset "0") ->
    (*FIXME: make sure the typetransformation works.*)
    (*FIXME: pass a right type to get_sexp_value and llocate_tmp here*)
    if (String.equal w "w32") then
      get_sexp_value src t
    else
      {v=Cast (t, allocate_tmp (get_sexp_value src Sint32));t}
  | Sexp.List [Sexp.Atom f; Sexp.Atom w; arg]
    when (String.equal f "SExt") && (String.equal w "w64") ->
    get_sexp_value arg t (*TODO: make sure this ignorance is ok *)
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "Add") ->
    begin (* Prefer a variable in the left position
             due to the weird VeriFast type inference rules.*)
      match lhs with
      | Sexp.Atom str when is_int str ->
        (* As a hack: special hundling for 64bit -10
           TODO: generalize*)
        if (String.equal str "18446744073709551606") then
          {v=Bop (Sub,(get_sexp_value rhs t),{v=(Int 10);t});t}
          else
            let ival = int_of_string str in (* avoid overflow *)
            if ival > 2147483648 then
              {v=Bop (Sub,(get_sexp_value rhs t),
                      {v=(Int (2*2147483648 - ival));t});t}
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
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; Sexp.Atom lhs; rhs;]
    when (String.equal f "Concat") && (String.equal lhs "0") ->
    get_sexp_value rhs t
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
          ~f:(fun {fname;value;_} (name,t) ->
              assert(String.equal name fname);
              {name;value=(get_struct_val_value value t)})
      in
      {v=Struct (strname, fields);t}
    end
  | _ -> match valu.full with
    | Some v -> get_sexp_value v t
    | None -> {t;v=Undef}

let update_ptee_variants nval older =
  match nval with
  | {value={t=Unknown;v=_};_} -> older
  | _ ->
    match older with
    | [{value={t=Unknown;v=_};_}] -> [nval]
    | _ -> nval::older

let rec add_to_known_addresses (base_value: tterm) breakdown addr callid depth =
  begin match base_value.t with
  | Ptr (Str (_,fields)) ->
    let fields = List.fold fields ~init:String.Map.empty
        ~f:(fun fields (name,t) ->
            String.Map.add fields ~key:name ~data:t)
    in
    List.iter breakdown ~f:(fun {fname;value;addr} ->
        let ftype = match String.Map.find fields fname with
          | Some t -> t | None -> Unknown
        in
        let b_value = {t=Ptr ftype;
                       v=Addr {t=ftype;
                               v=Str_idx ({t=get_pointee base_value.t;
                                           v=Deref base_value},fname)}}
        in
        add_to_known_addresses b_value value.break_down addr callid (depth+1))
  | _ ->
    if (List.length breakdown) <> 0 then
      printf "%s : %s type with %d fields" (render_tterm base_value)
        (ttype_to_str base_value.t) (List.length breakdown);
    assert((List.length breakdown) = 0)
  end;
  (* The order is important here, if we do not want to replace
     the pointer to the base_value by a pointer to its field. *)
  let prev = match Int64.Map.find !known_addresses addr with
    | Some value -> value
    | None -> []
  in
  known_addresses := Int64.Map.add !known_addresses
      ~key:addr ~data:(update_ptee_variants
                         {value=base_value; callid; str_depth=depth}
                         prev)

let get_basic_vars ftype_of tpref =
  let get_vars known_vars (call:Trace_prefix.call_node) =
    let get_arg_pointee_vars ptee ptee_type accumulator =
      let before_vars =
        get_vars_from_struct_val ptee.before ptee_type accumulator
      in
      get_vars_from_struct_val ptee.after ptee_type before_vars
    in
    let get_ret_pointee_vars ptee ptee_type accumulator =
      assert(ptee.before.full = None);
      assert(ptee.before.break_down = []);
      (*TODO: use another name generator to distinguish
        ret pointee stubs from the args *)
      get_vars_from_struct_val ptee.after ptee_type accumulator
    in
    let complex_value_vars value ptr (t:ttype) is_ret acc =
      match ptr with
      | Nonptr -> get_vars_from_plain_val value (type_guess_of_ttype t) acc
      | Funptr _ -> acc
      | Apathptr ->
        acc
      | Curioptr ptee ->
        let ptee_type = get_pointee t in
        if is_ret then begin
          get_ret_pointee_vars ptee ptee_type acc
        end
        else get_arg_pointee_vars ptee ptee_type acc
    in
    assert((List.length call.args) =
           (List.length (ftype_of call.fun_name).arg_types));
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
           (get_var_decls_of_sexp ctxt {s=Noidea;w=Sure W1;precise=Boolean} vars)) in
    let call_ctxt_vars =
      List.fold call.call_context ~f:add_vars_from_ctxt ~init:ret_vars in
    let ret_ctxt_vars =
      List.fold call.ret_context ~f:add_vars_from_ctxt ~init:call_ctxt_vars in
    ret_ctxt_vars
  in
  let hist_vars = (List.fold tpref.history
                     ~init:String.Map.empty ~f:get_vars) in
  let tip_vars = (List.fold tpref.tip_calls ~init:hist_vars ~f:get_vars) in
  tip_vars

let allocate_tip_ret_dummies ftype_of tip_calls (rets:var_spec Int.Map.t) =
  let alloc_dummy_for_call (rets, acc_dummies) call =
    let ret_type = get_fun_ret_type ftype_of call.fun_name in
    let add_the_dummy_to_tables value =
      let name = (Int.Map.find_exn rets call.id).name in
      let dummy_name = "tip_ret_dummy"^(Int.to_string call.id) in
      (Int.Map.add rets ~key:call.id
         ~data:{name;value={t=ret_type;v=Addr {v=Id dummy_name;
                                               t=get_pointee ret_type}}},
       Int.Map.add acc_dummies ~key:call.id
         ~data:{name=dummy_name;value=value})
    in
    match call.ret with
    | Some {value=_;ptr=Apathptr} ->
      add_the_dummy_to_tables {t=get_pointee ret_type;v=Undef}
    | Some {value=_;ptr=Curioptr ptee} ->
      let t = get_pointee ret_type in
      add_the_dummy_to_tables (get_struct_val_value ptee.after t)
    | _ -> (rets, acc_dummies)
  in
  List.fold tip_calls ~init:(rets, Int.Map.empty) ~f:alloc_dummy_for_call

let allocate_rets ftype_of tpref =
  let alloc_call_ret acc_rets call =
    let ret_type = get_fun_ret_type ftype_of call.fun_name in
    match call.ret with
    | Some {value;ptr;} ->
      let name = "ret"^(Int.to_string call.id) in
      let data = match ptr with
        | Nonptr -> {name;value=get_sexp_value value ret_type}
        | Funptr _ -> failwith "TODO:support funptr retuns."
        | Apathptr ->
          let addr = Int64.of_string (Sexp.to_string value) in
          add_to_known_addresses {t=ret_type;v=Id name} [] addr call.id 0;
          {name;value={t=ret_type;v=Addr {t=get_pointee ret_type;v=Undef}}}
        | Curioptr ptee ->
          let addr = Int64.of_string (Sexp.to_string value) in
          add_to_known_addresses {v=Id name;t=ret_type}
            ptee.after.break_down addr call.id 0;
          {name;value={t=ret_type;v=Addr (get_struct_val_value
                                            ptee.after (get_pointee ret_type))}}
      in
      Int.Map.add acc_rets ~key:call.id ~data
    | None -> acc_rets
  in
  let rets =
    List.fold (tpref.tip_calls@(List.rev tpref.history))
      ~init:Int.Map.empty ~f:alloc_call_ret
  in
  List.fold tpref.tip_calls ~init:rets
    ~f:(fun rets call ->
        if call.ret = None then
          rets
        else
          let ret = Int.Map.find_exn rets call.id in
          Int.Map.add rets ~key:call.id ~data:{ret with name="tip_ret"})

let allocate_args ftype_of tpref arg_name_gen =
  let alloc_call_args (call:Trace_prefix.call_node) =
    let alloc_arg addr str_value tterm =
      match Int64.Map.find !known_addresses addr with
      | Some spec -> known_addresses :=
          Int64.Map.add !known_addresses
            ~key:addr ~data:(List.map spec ~f:(fun spec ->
                {spec with value=update_tterm spec.value tterm}));
        None
      | None -> let p_name = arg_name_gen#generate in
        add_to_known_addresses
          {v=Addr {v=Id p_name;t=tterm.t};t=Ptr tterm.t}
          str_value.break_down
          addr call.id 0;
        Some {name=p_name;value=tterm}
    in
    List.filter_mapi call.args ~f:(fun i {aname=_;value;ptr;} ->
        match ptr with
        | Nonptr -> None
        | Funptr _ -> None
        | Apathptr ->
          let addr = Int64.of_string (Sexp.to_string value) in
          let t = get_fun_arg_type ftype_of call.fun_name i in
          let ptee_type = get_pointee t in
          alloc_arg addr {full=None;break_down=[]} {v=Undef;t=ptee_type;}
        | Curioptr ptee ->
          let addr = Int64.of_string (Sexp.to_string value) in
          let t = get_fun_arg_type ftype_of call.fun_name i in
          let ptee_type = get_pointee t in
          alloc_arg addr ptee.before (get_struct_val_value ptee.after ptee_type))
  in
  List.join (List.map (tpref.history@tpref.tip_calls) ~f:alloc_call_args)

let compose_fcall_preamble ftype_of call args tmp_gen =
  (List.map (ftype_of call.fun_name).lemmas_before ~f:(fun l -> l args tmp_gen))

let find_first_known_address addr =
  Option.map (Int64.Map.find !known_addresses addr)
    ~f:(fun lst -> (List.hd_exn lst).value)

let find_exn_first_known_address addr =
  (List.hd_exn (Int64.Map.find_exn !known_addresses addr)).value

let extract_fun_args ftype_of (call:Trace_prefix.call_node) =
  let get_allocated_arg (arg: Trace_prefix.arg) arg_type =
    let arg_var = find_first_known_address
        (Int64.of_string (Sexp.to_string arg.value)) in
    let ptee_t = get_pointee arg_type in
    match arg_var with
    | Some n -> n
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
        | Curioptr _ ->
          get_allocated_arg arg a_type)

let compose_post_lemmas ~is_tip ftype_of call ret_spec args tmp_gen =
  let ret_spec = match ret_spec with
    | Some ret_spec -> ret_spec
    | None -> {name="";value={v=Undef;t=Unknown}}
  in
  let result = render_tterm ret_spec.value in
  List.map (ftype_of call.fun_name).lemmas_after
    ~f:(fun l -> l {ret_name=ret_spec.name;ret_val=result;
                    args;tmp_gen;is_tip})

let compose_args_post_conditions (call:Trace_prefix.call_node) =
  List.filter_map call.args ~f:(fun arg ->
      match arg.ptr with
      | Nonptr -> None
      | Funptr _ -> None
      | Apathptr -> None
      | Curioptr ptee ->
        let out_arg =
          let key = Int64.of_string (Sexp.to_string arg.value) in
          find_exn_first_known_address key
        in
        Some {lhs={v=simplify_term (Deref out_arg);t=Ptr out_arg.t};
              rhs=(get_struct_val_value ptee.after (get_pointee out_arg.t))})

let gen_unique_tmp_name unique_postfix prefix =
  prefix ^ unique_postfix

let find_last_known_address_before_call addr call_id =
  Option.map (Int64.Map.find !known_addresses addr)
    ~f:(fun lst ->
        List.fold lst ~init:({v=Undef;t=Unknown},0)
          ~f:(fun (max_el,max_id)
               spec ->
               if spec.callid <= call_id && max_id < spec.callid then
                 (spec.value,spec.callid)
               else
                 (max_el,max_id)))

let find_last_known_whole_address_before_call addr call_id =
  Option.map (Int64.Map.find !known_addresses addr)
    ~f:(fun lst ->
        List.fold lst ~init:({v=Undef;t=Unknown},-1)
          ~f:(fun (max_el,max_id)
               spec ->
               if spec.str_depth = 0 && spec.callid <= call_id && max_id < spec.callid then
                 (spec.value,spec.callid)
               else
                 (max_el,max_id)))

let take_extra_ptrs_into_account ptrs callid =
  List.filter_map ptrs ~f:(fun {pname;value;ptee} ->
      match find_last_known_whole_address_before_call value callid with
      | None -> None
      | Some (x,_) ->
        match get_struct_val_value ptee.before (get_pointee x.t) with
        | {v=Undef;t=_} -> None
        | y -> Some {lhs={v=Deref x;t=y.t};rhs=y})

let extract_common_call_context
    ~is_tip ftype_of call ret_spec args unique_postfix =
  let tmp_gen = gen_unique_tmp_name unique_postfix in
  let ret_type = get_fun_ret_type ftype_of call.fun_name in
  let arg_names = List.map args ~f:render_tterm in
  let pre_lemmas = compose_fcall_preamble ftype_of call arg_names tmp_gen in
  let application = simplify_term (Apply (call.fun_name,args)) in
  let extra_pre_conditions =
    take_extra_ptrs_into_account call.extra_ptrs call.id
  in
  let post_lemmas =
    compose_post_lemmas
      ~is_tip ftype_of call ret_spec arg_names tmp_gen
  in
  let ret_name = match ret_spec with
    | Some ret_spec -> Some ret_spec.name
    | None -> None
  in
  {extra_pre_conditions;pre_lemmas;application;post_lemmas;ret_name;ret_type}

let extract_hist_call ftype_of call rets =
  let args = extract_fun_args ftype_of call in
  let args_post_conditions = compose_args_post_conditions call in
  let uniq = string_of_int call.id in
  match Int.Map.find rets call.id with
  | Some ret ->
    {context=extract_common_call_context
         ~is_tip:false ftype_of call (Some ret) args uniq;
     result={args_post_conditions;ret_val=ret.value}}
  | None ->
    {context=extract_common_call_context
         ~is_tip:false ftype_of call None args uniq;
     result={args_post_conditions;ret_val={t=Unknown;v=Undef;}}}

let convert_ctxt_list l = List.map l ~f:(fun e ->
    (get_sexp_value e Boolean))

let split_common_assumptions a1 a2 =
  let as1 = convert_ctxt_list a1 in
  let as2 = convert_ctxt_list a2 in
  List.partition_tf as1 ~f:(fun assumption ->
      List.exists as2 ~f:(fun other -> other = assumption))

let extract_tip_calls ftype_of calls rets =
  let call = List.hd_exn calls in
  let args = extract_fun_args ftype_of call in
  let context = extract_common_call_context
      ~is_tip:true ftype_of call (Int.Map.find rets call.id) args "tip"
  in
  let get_ret_val call =
    match Int.Map.find rets call.id with
    | Some ret -> ret.value
    | None -> {t=Unknown;v=Undef;}
  in
  let results =
    match calls with
    | [] -> failwith "There must be at least one tip call."
    | tip :: [] ->
      let args_post_conditions = compose_args_post_conditions tip in
      [{args_post_conditions;
        ret_val=get_ret_val tip;
        post_statements=convert_ctxt_list tip.ret_context;}]
    | tip1 :: tip2 :: [] ->
      let args_post_conditions1 = compose_args_post_conditions tip1 in
      let args_post_conditions2 = compose_args_post_conditions tip2 in
      [{args_post_conditions=args_post_conditions1;
        ret_val=get_ret_val tip1;
        post_statements=convert_ctxt_list tip1.ret_context;};
       {args_post_conditions=args_post_conditions2;
        ret_val=get_ret_val tip2;
        post_statements=convert_ctxt_list tip2.ret_context;}]
    | _ -> failwith "More than two tip calls is not supported."
  in
  {context;results}

let extract_calls_info ftype_of tpref rets =
  let hist_funs =
    (List.map tpref.history ~f:(fun call ->
         extract_hist_call ftype_of call rets))
  in
  let tip_calls = extract_tip_calls ftype_of tpref.tip_calls rets in
  hist_funs, tip_calls

let collect_context pref =
  (List.join (List.map pref.history ~f:(fun call ->
      (convert_ctxt_list call.call_context) @
      (convert_ctxt_list call.ret_context)))) @
  (match pref.tip_calls with
   | hd :: [] -> (convert_ctxt_list hd.call_context)
   | hd1 :: hd2 :: [] ->
     let call_context = convert_ctxt_list hd1.call_context in
     assert (call_context = (convert_ctxt_list hd2.call_context));
     call_context
   | [] -> failwith "There must be at least one tip call."
   | _ -> failwith "More than two tip alternative tipcalls are not supported.")

let strip_context call =
  (* TODO: why do we erase the return value? *)
  {call with ret = None; call_context = []; ret_context = [];}

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
      {history=[]; tip_calls = List.map pref.tip_calls ~f:strip_context}
    else
      match last_relevant_seg pref.history [] with
      | bnd :: rest ->
        {history = strip_context bnd :: rest; tip_calls = pref.tip_calls}
      | [] -> pref

let is_the_last_function_finishing pref finishing_fun =
  String.equal (List.hd_exn pref.tip_calls).fun_name finishing_fun

let distribute_ids pref =
  let tips_start_from = List.length pref.history in
  {history =
     List.mapi pref.history ~f:(fun i call -> {call with id = i});
   tip_calls =
     List.mapi pref.tip_calls ~f:(fun i call ->
         {call with id = tips_start_from + i})}

let ttype_of_guess = function
  | {precise=Unknown;s=Tentative Sgn;w;}
  | {precise=Unknown;s=Sure Sgn;w;} -> begin match w with
      | Noidea -> Sunknown
      | Sure W1 | Tentative W1 -> Boolean
      | Sure W8 | Tentative W8 -> Sint8
      | Sure W16 | Tentative W16 -> Sunknown
      | Sure W32 | Tentative W32 -> Sint32
      end
  | {precise=Unknown;s=Tentative Unsgn;w;}
  | {precise=Unknown;s=Sure Unsgn;w;} -> begin match w with
      | Noidea -> Uunknown
      | Sure W1 | Tentative W1 -> Boolean
      | Sure W8 | Tentative W8 -> Uint8
      | Sure W16 | Tentative W16 -> Uint16
      | Sure W32 | Tentative W32 -> Uint32
      end
  | {precise=Unknown;s=Noidea;w=Sure W1;}
  | {precise=Unknown;s=Noidea;w=Tentative W1;} -> Boolean
  | {precise=Unknown;s=Noidea;w=_;} -> Unknown
  | {precise;s=_;w=_} -> precise

let typed_vars_to_varspec free_vars =
  List.fold (String.Map.data free_vars) ~init:String.Map.empty
    ~f:(fun acc {vname;t;} ->
        String.Map.add acc ~key:vname
          ~data:{name=vname;value={v=Undef;t=ttype_of_guess t}})

let build_ir fun_types fin preamble boundary_fun finishing_fun =
  let ftype_of fun_name =
    match String.Map.find fun_types fun_name with
    | Some spec -> spec
    | None -> failwith ("unknown function " ^ fun_name)
  in
  let pref = get_relevant_segment
      (Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin))
      boundary_fun
  in
  let pref = distribute_ids pref in
  let finishing = is_the_last_function_finishing pref finishing_fun in
  let preamble = preamble in
  let export_point = "export_point" in
  let free_vars = get_basic_vars ftype_of pref in
  let arguments = allocate_args ftype_of pref (name_gen "arg") in
  let rets = allocate_rets ftype_of pref in
  (* let (rets, tip_dummies) = allocate_tip_ret_dummies ftype_of pref.tip_calls rets in *)
  let (hist_calls,tip_call) = extract_calls_info ftype_of pref rets in
  let tmps = !allocated_tmp_vals in
  let context_assumptions = collect_context pref in
  let cmplxs = !allocated_complex_vals in
  let free_vars = typed_vars_to_varspec free_vars in
  {preamble;free_vars;arguments;tmps;
   cmplxs;context_assumptions;hist_calls;tip_call;
   export_point;finishing}
