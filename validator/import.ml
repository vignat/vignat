open Core.Std
open Trace_prefix
open Ir
open Fspec_api

let do_log = true

let log str =
  if do_log then Out_channel.with_file ~append:true "import.log" ~f:(fun f ->
      Out_channel.output_string f str)
  else ()

let lprintf fmt = ksprintf log fmt

type 'x confidence = Sure of 'x | Tentative of 'x | Noidea

type t_width = W1 | W8 | W16 | W32
type t_sign = Sgn | Unsgn
type type_guess = {w:t_width confidence;
                   s:t_sign confidence;
                   precise: ttype}

type typed_var = {vname:string; t: type_guess;}

type address_spec = {value:tterm; callid:int; str_depth:int; tt:ttype}

let known_addresses : address_spec list Int64.Map.t ref = ref Int64.Map.empty

let infer_signed_type w =
  if String.equal w "w32" then Sint32
  else if String.equal w "w8" then Sint8
  else Sunknown

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
                                     ~data:(remove_defs def))
      | hd :: tl -> merge_defs (get_defs hd) (do_list tl)
      | [] -> String.Map.empty
    in
    match sexp with
    | Sexp.List lst -> do_list lst
    | Sexp.Atom _ -> String.Map.empty
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
    let new_map_expanded = List.map (Map.to_alist map) ~f:(fun (name,el) -> (name, expand_exp el defs)) in
    let changed =
      List.exists (List.map new_map_expanded ~f:(Fn.compose snd snd)) ~f:Fn.id
    in
    let new_map =
      String.Map.of_alist_exn (List.map new_map_expanded
                                 ~f:(fun (name,(new_el,changed)) -> (name,new_el)))
    in
    (new_map,changed)
  in
  let rec cross_expand_defs_fixp defs =
    let (new_defs, expanded) = expand_map defs defs in
    if expanded then cross_expand_defs_fixp new_defs
    else defs
  in
  let map_expandable map defs =
    List.exists (String.Map.data map) ~f:(fun el -> (snd (expand_exp el defs)))
  in
  let defs = get_defs sexp in
  let defs = cross_expand_defs_fixp defs in
  if (map_expandable defs defs) then begin
    lprintf "failed expansion on sexp: \n%s\n" (Sexp.to_string sexp);
    lprintf "defs: ";
    Map.iter (get_defs sexp) ~f:(fun ~key ~data ->
        lprintf "%s ::: %s\n" key (Sexp.to_string data));
    lprintf "expanded defs: ";
    Map.iter defs ~f:(fun ~key ~data ->
        lprintf "%s ::: %s\n" key (Sexp.to_string data));
    failwith ("incomplete map expansion for " ^ (Sexp.to_string sexp));
  end;
  (fst (expand_exp (remove_defs sexp) defs))

let get_fun_arg_type (ftype_of,type_guesses) call arg_num =
  match List.nth_exn (ftype_of call.fun_name).arg_types arg_num with
  | Static t -> t
  | Dynamic ts -> List.nth_exn ts (Int.Map.find_exn
                                     (Int.Map.find_exn type_guesses call.id)
                                     arg_num)

let get_fun_extra_ptr_type (ftype_of,_) call exptr_name =
  match List.Assoc.find (ftype_of call.fun_name).extra_ptr_types
          ~equal:String.equal exptr_name with
  | Some t -> t
  | None -> failwith ("Could not find extra_ptr " ^ exptr_name ^
                      " type for function " ^ call.fun_name)

let get_fun_ret_type (ftype_of, _) call = (ftype_of call.fun_name).ret_type

let get_num_args (ftype_of, _) call =
  List.length (ftype_of call.fun_name).arg_types

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
        | _ ->
          lprintf "ZExt may have only one argument: %s\n" (Sexp.to_string exp);
          failwith "ZExt may have only one argument (besides w..)."
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
  let decls = get_var_decls_of_sexp (expand_shorted_sexp v) type_guess known_vars in
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
let allocated_dummies = ref []

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
let guess_type exp t =
  lprintf "guessing for %s, know %s\n" (Sexp.to_string exp) (ttype_to_str t);
  match t with
  | Uunknown -> begin match exp with
      | Sexp.List [Sexp.Atom f; Sexp.Atom w; _; _]
        when (String.equal f "Concat") && (String.equal w "w32") -> Uint32
      | _ -> t
    end
  | _ -> t


let rec guess_type_l exps t =
  match exps with
  | hd :: tl -> begin match guess_type hd t with
      | Unknown -> guess_type_l tl t
      | s -> s
    end
  | [] -> Unknown

let find_first_known_address addr tt =
  lprintf "looking for first *%Ld\n" addr;
  Option.map (Int64.Map.find !known_addresses addr)
    ~f:(fun lst ->
        (List.hd_exn
           (List.filter lst ~f:(fun x ->
                match x.tt, tt with
                | _, Unknown -> true
                | t1, t2 ->
                  if (t1 <> t2) then
                    lprintf "discarding: %s != %s\n"
                      (ttype_to_str t1) (ttype_to_str t2);
                  t1 = t2))).value)

let find_first_known_address_or_dummy addr t =
  match find_first_known_address addr t with
  | Some tt -> tt
  | None -> {v=Utility (Ptr_placeholder addr); t=Ptr t}

let rec get_sexp_value exp t =
  let exp = expand_shorted_sexp exp in
  let exp = eliminate_false_eq_0 exp t in
  match exp with
  | Sexp.Atom v ->
    begin
      let t = match t with
        |Unknown|Sunknown|Uunknown -> guess_type exp t
        |_ -> t
      in
      match t with
      | Sint32 -> {v=Int (get_sint_in_bounds v);t}
      | _ ->
        if String.equal v "true" then {v=Bool true;t=Boolean}
        else if String.equal v "false" then {v=Bool false;t=Boolean}
        (*FIXME: deduce the true integer type for the value: *)
        else if is_int v then
          let addr = (Int64.of_int (int_of_string v)) in
          if addr = 0L then {v=Int 0; t}
          else
            match t with
            | Ptr x ->
              find_first_known_address_or_dummy addr x
            | _ -> {v=Int (int_of_string v);t}
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
  | Sexp.List [Sexp.Atom f; Sexp.Atom offset; src;]
    when (String.equal f "Extract") && (String.equal offset "0") ->
    get_sexp_value src Boolean
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
    let ty = guess_type_l [lhs;rhs] Unknown in
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
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "And") ->
    begin
      match rhs with
      | Sexp.Atom n when is_int n ->
        {v=Bop (Bit_and,(get_sexp_value lhs Uint32),(get_sexp_value rhs Uint32));t=Uint32}
      | _ ->
        let ty = guess_type_l [lhs;rhs] t in
        lprintf "interesting And case{%s}: %s "
          (ttype_to_str ty) (Sexp.to_string exp);
        if ty = Boolean then
          {v=Bop (And,(get_sexp_value lhs ty),(get_sexp_value rhs ty));t=ty}
        else
          {v=Bop (Bit_and,(get_sexp_value lhs ty),(get_sexp_value rhs ty));t=ty}
    end
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; Sexp.Atom lhs; rhs;]
    when (String.equal f "Concat") && (String.equal lhs "0") ->
    get_sexp_value rhs t
  | _ ->
    begin match get_var_name_of_sexp exp with
      | Some name -> {v=Id name;t}
      | None ->
        let t = match t with
          |Unknown|Sunknown|Uunknown -> guess_type exp t
          |_ -> t
        in
        make_cmplx_val exp t
    end

let rec get_struct_val_value valu t =
  match t with
  | Str (strname, fields) ->
    begin
    (*   match get_var_name_of_sexp valu.full with *)
    (* | Some name -> {v=Id name;t} *)
    (* | None -> <^^^ this was working a while ago, may be it should be
       left somewhere *)
      lprintf "Destruct: %s; Need %d fields got %d fields.\n" strname
        (List.length fields) (List.length valu.break_down);
      if List.length valu.break_down <>
         List.length fields then begin
        lprintf "%s expects %d fields but found only %d"
          strname (List.length fields) (List.length valu.break_down);
        failwith ("Break down of " ^ strname ^
                  " does not correspond to its type.");
      end;
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
  | Ptr (Str (_,fields) as ptee_type) ->
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
                               v=Str_idx ({t=ptee_type;
                                           v=Deref base_value},fname)}}
        in
        add_to_known_addresses b_value value.break_down addr callid (depth+1))
  | _ ->
    if (List.length breakdown) <> 0 then
      lprintf "%s : %s type with %d fields" (render_tterm base_value)
        (ttype_to_str base_value.t) (List.length breakdown);
    assert((List.length breakdown) = 0)
  end;
  (* The order is important here, if we do not want to replace
     the pointer to the base_value by a pointer to its field. *)
  lprintf "allocating *%Ld = %s\n" addr (render_tterm base_value);
  let prev = match Int64.Map.find !known_addresses addr with
    | Some value -> value
    | None -> []
  in
  known_addresses := Int64.Map.add !known_addresses
      ~key:addr ~data:(update_ptee_variants
                         {value=base_value; callid; str_depth=depth;
                          tt=get_pointee base_value.t}
                         prev)

let get_basic_vars ftype_of tpref =
  let get_vars known_vars (call:Trace_prefix.call_node) =
    let get_arg_pointee_vars ptee ptee_type accumulator =
      let before_vars =
        get_vars_from_struct_val ptee.before ptee_type accumulator
      in
      get_vars_from_struct_val ptee.after ptee_type before_vars
    in
    let get_extra_ptr_pointee_vars ptee ptee_type accumulator =
      match ptee with
      | Opening x -> get_vars_from_struct_val x ptee_type accumulator
      | Closing x -> get_vars_from_struct_val x ptee_type accumulator
      | Changing (a,b) ->
        get_vars_from_struct_val a ptee_type
          (get_vars_from_struct_val b ptee_type accumulator)
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
    if (List.length call.args <> get_num_args ftype_of call) then
      failwith ("Wrong number of arguments in the plugin for function " ^
                call.fun_name);
    let arg_vars = List.foldi call.args ~init:known_vars
        ~f:(fun i acc arg ->
            let arg_type = get_fun_arg_type ftype_of call i in
            complex_value_vars arg.value arg.ptr arg_type false acc)
    in
    let extra_ptr_vars = List.fold call.extra_ptrs ~init:arg_vars
        ~f:(fun acc {pname;value;ptee} ->
            let ptee_type =
              get_fun_extra_ptr_type ftype_of call pname in
          get_extra_ptr_pointee_vars ptee ptee_type acc)
    in
    let ret_vars = match call.ret with
      | Some ret ->
        complex_value_vars
          ret.value ret.ptr
          (get_fun_ret_type ftype_of call) true extra_ptr_vars
      | None -> extra_ptr_vars in
    let add_vars_from_ctxt vars ctxt =
      map_set_n_update_alist vars
        (make_name_alist_from_var_decls
           (get_var_decls_of_sexp
              (expand_shorted_sexp ctxt)
              {s=Noidea;w=Sure W1;precise=Boolean} vars)) in
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
    let ret_type = get_fun_ret_type ftype_of call in
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
    let ret_type = get_fun_ret_type ftype_of call in
    match call.ret with
    | Some {value;ptr;} ->
      let name = "ret"^(Int.to_string call.id) in
      let data = match ptr with
        | Nonptr -> {name;value=get_sexp_value value ret_type}
        | Funptr _ -> failwith "TODO:support funptr retuns."
        | Apathptr ->
          let addr = Int64.of_string (Sexp.to_string value) in
          if (addr = 0L) then
            {name;value={t=ret_type;v=Zeroptr}}
          else begin
            add_to_known_addresses {t=ret_type;v=Id name} [] addr call.id 0;
            {name;value={t=ret_type;v=Addr {t=get_pointee ret_type;v=Undef}}}
          end
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

let alloc_or_update_address addr name str_value (tterm:tterm) call_id =
  lprintf "looking for *%Ld\n" addr;
  match Int64.Map.find !known_addresses addr with
  | Some specs -> begin
      known_addresses := Int64.Map.remove !known_addresses addr;
      match List.find specs ~f:(fun spec -> spec.tt = tterm.t) with
      | Some spec ->
        add_to_known_addresses (update_tterm spec.value tterm)
          str_value.break_down addr call_id 0;
        None
      | None -> (* The existing spec does not contain a piece of the type tterm.t
                   this means it is inferior to tterm, and if we add tterm, it will
                   also re-add the inferior parts.
                   TODO: there may be a problem in relating the added tterm to the
                   spec that was there before. *)
        add_to_known_addresses
          {v=Addr {v=Id name;t=tterm.t};t=Ptr tterm.t}
          str_value.break_down
          addr call_id 0;
        Some {name=name;value=tterm}
    end
  | None ->
    add_to_known_addresses
      {v=Addr {v=Id name;t=tterm.t};t=Ptr tterm.t}
      str_value.break_down
      addr call_id 0;
    Some {name=name;value=tterm}

let allocate_extra_ptrs ftype_of tpref =
  let alloc_call_extra_ptrs call =
    let alloc_extra_ptr p_name addr str_value tterm =
      alloc_or_update_address addr p_name str_value tterm call.id
    in
    List.filter_map call.extra_ptrs ~f:(fun {pname;value;ptee} ->
        let addr = value in
        let ptee_type = get_fun_extra_ptr_type ftype_of call pname in
        match ptee with
        | Opening _ ->
          alloc_extra_ptr (pname ^ call.fun_name)
            addr {full=None;break_down=[]} {v=Undef;t=ptee_type}
        | Closing x ->
          alloc_extra_ptr (pname ^ "_" ^ call.fun_name ^
                           (Int64.to_string addr)) addr x
            (get_struct_val_value x ptee_type)
        | Changing (x,_) ->
          lprintf "allocating extra ptr: %s addr %Ld : %s\n"
            pname addr (ttype_to_str ptee_type);
          alloc_extra_ptr (pname ^ "_" ^ call.fun_name ^
                           (Int64.to_string addr)) addr x
            (get_struct_val_value x ptee_type))
  in
  List.join (List.map (tpref.history@tpref.tip_calls) ~f:alloc_call_extra_ptrs)

let allocate_args ftype_of tpref arg_name_gen =
  let alloc_call_args (call:Trace_prefix.call_node) =
    let alloc_arg addr str_value tterm =
      lprintf "looking for *%Ld :" addr;
      match Int64.Map.find !known_addresses addr with
      | Some spec -> known_addresses :=
          Int64.Map.add !known_addresses
            ~key:addr ~data:(List.map spec ~f:(fun spec ->
                {spec with value=update_tterm spec.value tterm}));
        lprintf "found some, adding\n";
        None
      | None -> let p_name = arg_name_gen#generate in
        add_to_known_addresses
          {v=Addr {v=Id p_name;t=tterm.t};t=Ptr tterm.t}
          str_value.break_down
          addr call.id 0;
        lprintf "found none, inserting\n";
        Some {name=p_name;value=tterm}
    in
    let alloc_dummy_nested_ptr ptr_addr ptee_addr ptee_t =
      lprintf "looking for *%Ld\n" ptr_addr;
      match Int64.Map.find !known_addresses ptr_addr with
      | Some _ -> None
      | None ->
        lprintf "looking for *%Ld\n" ptee_addr;
        match Int64.Map.find !known_addresses ptee_addr with
        | Some _ -> failwith "nested ptr value dynamics too complex :/"
        | None -> let p_name = arg_name_gen#generate in
          lprintf "allocating nested %Ld -> %s = &%Ld:%s\n"
            ptr_addr p_name ptee_addr (ttype_to_str (Ptr ptee_t));
          add_to_known_addresses
            {v=Addr {v=Id p_name;t=Ptr ptee_t};t=Ptr (Ptr ptee_t)}
          []
          ptr_addr call.id 0;
          add_to_known_addresses
            {v=Id p_name;t=Ptr ptee_t}
            []
            ptee_addr call.id 0;
        Some {name=p_name;value={v=Undef;t=Ptr ptee_t}}
    in
    List.filter_mapi call.args ~f:(fun i {aname=_;value;ptr;} ->
        match ptr with
        | Nonptr -> None
        | Funptr _ -> None
        | Apathptr ->
          let addr = Int64.of_string (Sexp.to_string value) in
          let t = get_fun_arg_type ftype_of call i in
          let ptee_type = get_pointee t in
          alloc_arg addr {full=None;break_down=[]} {v=Undef;t=ptee_type;}
        | Curioptr ptee ->
          let addr = Int64.of_string (Sexp.to_string value) in
          let t = get_fun_arg_type ftype_of call i in
          let ptee_type = get_pointee t in
          let ptee_ptr_val = Option.map ptee.before.full
              ~f:(fun expr -> get_sexp_value expr ptee_type)
          in
          let ptee_ptr_val_after = Option.map ptee.after.full
              ~f:(fun expr -> get_sexp_value expr ptee_type)
          in
          match ptee_type, ptee_ptr_val with
            | Ptr ptee_ptee_t, Some {v=(Int x);t=_} when x <> 0 ->
              alloc_dummy_nested_ptr addr (Int64.of_int x) ptee_ptee_t
            | Ptr ptee_ptee_t, Some {v=Utility (Ptr_placeholder x);t=_}
              when x <> 0L ->
              alloc_dummy_nested_ptr addr x ptee_ptee_t
            | _ -> match ptee_type, ptee_ptr_val_after with
              | Ptr ptee_ptee_t, Some {v=(Int x);t=_} when x <> 0 ->
                alloc_dummy_nested_ptr addr (Int64.of_int x) ptee_ptee_t
              | Ptr ptee_ptee_t, Some {v=Utility (Ptr_placeholder x);t=_}
                when x <> 0L ->
                alloc_dummy_nested_ptr addr x ptee_ptee_t
              | _ -> alloc_arg addr ptee.before (get_struct_val_value
                                                   ptee.before ptee_type))
  in
  List.join (List.map (tpref.history@tpref.tip_calls) ~f:alloc_call_args)

let get_lemmas_before (ftype_of,_) call =
  (ftype_of call.fun_name).lemmas_before

let compose_fcall_preamble ftype_of call args arg_types tmp_gen is_tip =
  (List.map (get_lemmas_before ftype_of call) ~f:(fun l ->
       l {args;tmp_gen;is_tip;arg_types}))

let extract_fun_args ftype_of (call:Trace_prefix.call_node) =
  let get_allocated_arg (arg: Trace_prefix.arg) arg_type =
    let ptee_t = get_pointee arg_type in
    let arg_var = find_first_known_address
        (Int64.of_string (Sexp.to_string arg.value))
        ptee_t
    in
    match arg_var with
    | Some n -> n
    | None -> {v=Addr {v=(Id "arg??");t=ptee_t};t=arg_type}
  in
  List.mapi call.args
    ~f:(fun i arg ->
        let a_type = get_fun_arg_type ftype_of call i in
        match arg.ptr with
        | Nonptr -> get_sexp_value arg.value a_type
        | Funptr fname -> {v=Fptr fname;t=a_type}
        | Apathptr ->
          get_allocated_arg arg a_type
        | Curioptr ptee ->
          match a_type, ptee.before.full with
          | Ptr (Ptr t), Some addr ->
            begin (* Workaround for 2-level pointers args.*)
              let addr = get_sexp_value addr (Ptr t) in
              match addr with
              | {v=Int x;t=_} -> if (x = 0) then
                  get_allocated_arg arg a_type
                else begin
                  let key = Int64.of_int x in
                  match find_first_known_address key t with
                  | Some n -> {v=Addr n; t=Ptr t}
                  | None -> match find_first_known_address
                                    (Int64.of_string (Sexp.to_string arg.value))
                                    t
                    with
                    | Some n -> n
                    | None -> failwith ("nested pointer to unknown: " ^
                                        (Int.to_string x) ^ " -> " ^
                                        (Sexp.to_string arg.value))
                end
              | x -> get_allocated_arg arg a_type
            end
          | _ ->
            get_allocated_arg arg a_type)

let get_lemmas_after (ftype_of, _) call =
  (ftype_of call.fun_name).lemmas_after

let compose_post_lemmas ~is_tip ftype_of call ret_spec args arg_types tmp_gen =
  let ret_spec = match ret_spec with
    | Some ret_spec -> ret_spec
    | None -> {name="";value={v=Undef;t=Unknown}}
  in
  let result = render_tterm ret_spec.value in
  List.map (get_lemmas_after ftype_of call)
    ~f:(fun l -> l {ret_name=ret_spec.name;ret_val=result;
                    args;tmp_gen;is_tip;arg_types})

let deref_tterm {v;t} =
  {v = simplify_term (Deref {v;t});
   t = get_pointee t}

let compose_args_post_conditions (call:Trace_prefix.call_node) ftype_of =
  List.filter_mapi call.args ~f:(fun i arg ->
      match arg.ptr with
      | Nonptr -> None
      | Funptr _ -> None
      | Apathptr -> None
      | Curioptr ptee ->
        let key = Int64.of_string (Sexp.to_string arg.value) in
        let arg_type = (get_fun_arg_type ftype_of call i) in
        match find_first_known_address key (get_pointee arg_type) with
        | Some out_arg ->
          begin match get_struct_val_value
              ptee.after (get_pointee out_arg.t) with
          | {v=Int _;t=_} -> None
            (* Skip the two layer pointer.
               TODO: maybe be allow special case of Zeroptr here.*)
          | value ->
            Some {lhs=deref_tterm out_arg;
                  rhs=value}
          end
        | None -> None (* The variable is not allocated,
                          because it is a 2-layer pointer.*))

let compose_extra_ptrs_post_conditions (call:Trace_prefix.call_node)
  ftype_of =
  let gen_post_condition_of_struct_val (val_before : Ir.tterm) val_now =
    lprintf "postconditions for %s: %s\n" call.fun_name (ttype_to_str val_before.t);
    match get_struct_val_value
            val_now (get_pointee val_before.t) with
    | {v=Int _;t=_} -> None
    (* Skip the two layer pointer.
       TODO: maybe be allow special case of Zeroptr here.*)
    | value ->
      Some {lhs=deref_tterm val_before;
            rhs=value}
  in
  List.filter_map call.extra_ptrs ~f:(fun {pname;value;ptee} ->
      let key = value in
      match find_first_known_address key
              (get_fun_extra_ptr_type ftype_of call pname) with
      | Some extra_ptee ->
        begin match ptee with
          | Opening x -> gen_post_condition_of_struct_val extra_ptee x
          | Closing _ -> None
          | Changing (_,x) -> gen_post_condition_of_struct_val extra_ptee x
        end
      | None -> None (* The variable is not allocated,
                        because it is a 2-layer pointer.*))

let gen_unique_tmp_name unique_postfix prefix =
  prefix ^ unique_postfix

let find_last_known_address_before_call addr call_id =
  lprintf "looking for last *%Ld\n" addr;
  Option.map (Int64.Map.find !known_addresses addr)
    ~f:(fun lst ->
        List.fold lst ~init:({v=Undef;t=Unknown},0)
          ~f:(fun (max_el,max_id)
               spec ->
               if spec.callid <= call_id && max_id < spec.callid then
                 (spec.value,spec.callid)
               else
                 (max_el,max_id)))

let find_last_known_whole_address_before_call addr call_id tt =
  lprintf "looking for last whole *%Ld\n" addr;
  Option.map (Int64.Map.find !known_addresses addr)
    ~f:(fun lst ->
        List.fold lst ~init:({v=Undef;t=Unknown},-1,Int.max_value)
          ~f:(fun (max_el,max_id,min_depth) spec ->
              lprintf "for %Ld considering %s : %s (%s) -:- %s\n"
                addr (render_tterm spec.value)
                (ttype_to_str spec.tt)
                (ttype_to_str spec.value.t)
                (ttype_to_str tt);
               if (tt = Unknown ||
                   tt = spec.tt) &&
                  spec.str_depth < min_depth &&
                  (* spec.callid <= call_id && *)
                  max_id < spec.callid
               then
                 (spec.value,spec.callid,spec.str_depth)
               else
                 (max_el,max_id,min_depth)))

let take_extra_ptrs_into_account ptrs call ftype_of =
  let gen_eq_by_struct_val (var_ptr : Ir.tterm) value_now =
    match get_struct_val_value value_now (get_pointee var_ptr.t) with
    | {v=Undef;t=_} -> None
    | y -> Some {lhs=deref_tterm var_ptr;rhs=y}
  in
  List.filter_map ptrs ~f:(fun {pname;value;ptee} ->
      match find_last_known_whole_address_before_call
              value call.id
              (get_fun_extra_ptr_type ftype_of call pname) with
      | None -> None
      | Some (x,_,_) ->
        lprintf "settled on %s : %s\n"
          (render_tterm x) (ttype_to_str x.t);
        match ptee with
        | Opening o -> gen_eq_by_struct_val x o
        | Closing _ -> None
        | Changing (o,_) -> gen_eq_by_struct_val x o)

let take_arg_ptrs_into_account (args : Trace_prefix.arg list) call ftype_of =
  List.filter_mapi args ~f:(fun i arg ->
      match arg.ptr with
      | Nonptr -> None
      | Funptr _ -> None
      | Apathptr -> None
      | Curioptr ptee -> begin (* TODO: why nececerily a *whole* address?
                               See also take_extra_ptrs_into_account for the
                               same issue.*)
          let addr = Int64.of_string (Sexp.to_string arg.value) in
          match find_last_known_whole_address_before_call
                  addr call.id
                  (get_pointee (get_fun_arg_type ftype_of call i)) with
          | None -> None
          | Some (x,_,_) ->
            lprintf "arg. settled on %s : %s\n"
              (render_tterm x) (ttype_to_str x.t);
            match get_struct_val_value ptee.before (get_pointee x.t) with
            | {v=Undef;t=_} -> None
            | y -> Some {lhs={v=Deref x;t=y.t};rhs=y}
        end)

let insert_type_casts (free_vars:var_spec String.Map.t) = function
  | {v=Id name; t} -> begin
      match String.Map.find free_vars name with
      | Some v_spec ->
        if v_spec.value.t <> t then begin
          lprintf "add type cast %s -> %s for %s\n"
            (ttype_to_str v_spec.value.t)
            (ttype_to_str t)
            (render_tterm v_spec.value);
          Some {v=Cast (t, {v=Id name;t=v_spec.value.t});t=t}
        end else None
      | _ -> None
    end
  | _ -> None

let extract_common_call_context
    ~is_tip ftype_of call ret_spec args unique_postfix
    (free_vars:var_spec String.Map.t) =
  let args =
    List.map args ~f:(call_recursively_on_tterm (insert_type_casts free_vars))
  in
  let tmp_gen = gen_unique_tmp_name unique_postfix in
  let ret_type = get_fun_ret_type ftype_of call in
  let arg_names = List.map args ~f:render_tterm in
  let arg_types = List.map args ~f:(fun {t;v=_} -> t) in
  let pre_lemmas =
    compose_fcall_preamble ftype_of call arg_names arg_types tmp_gen is_tip
  in
  let application = simplify_term (Apply (call.fun_name,args)) in
  let extra_pre_conditions =
    (take_extra_ptrs_into_account call.extra_ptrs call ftype_of)@
    (take_arg_ptrs_into_account call.args call ftype_of)
  in
  let post_lemmas =
    compose_post_lemmas
      ~is_tip ftype_of call ret_spec arg_names arg_types tmp_gen
  in
  let ret_name = match ret_spec with
    | Some ret_spec -> Some ret_spec.name
    | None -> None
  in
  {extra_pre_conditions;pre_lemmas;application;post_lemmas;ret_name;ret_type}

let extract_hist_call ftype_of call rets free_vars =
  let args = extract_fun_args ftype_of call in
  let args_post_conditions = compose_args_post_conditions call ftype_of in
  let args_post_conditions =
    (compose_extra_ptrs_post_conditions call ftype_of)@
    args_post_conditions
  in
  let uniq = string_of_int call.id in
  match Int.Map.find rets call.id with
  | Some ret ->
    {context=extract_common_call_context
         ~is_tip:false ftype_of call (Some ret) args uniq
         free_vars;
     result={args_post_conditions;ret_val=ret.value}}
  | None ->
    {context=extract_common_call_context
         ~is_tip:false ftype_of call None args uniq
         free_vars;
     result={args_post_conditions;ret_val={t=Unknown;v=Undef;}}}

let convert_ctxt_list l = List.map l ~f:(fun e ->
    (get_sexp_value e Boolean))

let split_common_assumptions a1 a2 =
  let as1 = convert_ctxt_list a1 in
  let as2 = convert_ctxt_list a2 in
  List.partition_tf as1 ~f:(fun assumption ->
      List.exists as2 ~f:(fun other -> other = assumption))

let extract_tip_calls ftype_of calls rets free_vars =
  let call = List.hd_exn calls in
  let args = extract_fun_args ftype_of call in
  let context = extract_common_call_context
      ~is_tip:true ftype_of call (Int.Map.find rets call.id) args "tip"
      free_vars
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
      let args_post_conditions = compose_args_post_conditions tip ftype_of in
      [{args_post_conditions;
        ret_val=get_ret_val tip;
        post_statements=convert_ctxt_list tip.ret_context;}]
    | tip1 :: tip2 :: [] ->
      let args_post_conditions1 = compose_args_post_conditions tip1 ftype_of in
      let args_post_conditions2 = compose_args_post_conditions tip2 ftype_of in
      [{args_post_conditions=args_post_conditions1;
        ret_val=get_ret_val tip1;
        post_statements=convert_ctxt_list tip1.ret_context;};
       {args_post_conditions=args_post_conditions2;
        ret_val=get_ret_val tip2;
        post_statements=convert_ctxt_list tip2.ret_context;}]
    | _ ->
      List.map calls ~f:(fun tip ->
          {args_post_conditions = compose_args_post_conditions tip ftype_of;
           ret_val = get_ret_val tip;
           post_statements = convert_ctxt_list tip.ret_context})
      (* failwith ("More than two tip calls (" ^ *)
      (*           (string_of_int (List.length calls)) ^ *)
      (*           ") is not supported.") *)
  in
  lprintf "got %d results for tip-call\n" (List.length results);
  {context;results}

let extract_calls_info ftype_of tpref rets (free_vars:var_spec String.Map.t) =
  let hist_funs =
    (List.map tpref.history ~f:(fun call ->
         extract_hist_call ftype_of call rets free_vars))
  in
  let tip_calls = extract_tip_calls ftype_of tpref.tip_calls rets free_vars in
  hist_funs, tip_calls

let collect_context pref =
  (List.join (List.map pref.history ~f:(fun call ->
      (convert_ctxt_list call.call_context) @
      (convert_ctxt_list call.ret_context)))) @
  (match pref.tip_calls with
   | [] -> failwith "There must be at least one tip call."
   | hd :: tail -> let call_context = convert_ctxt_list hd.call_context in
     assert (List.for_all tail ~f:(fun tip ->
         call_context = convert_ctxt_list tip.call_context));
     call_context)
   (* | hd :: [] -> (convert_ctxt_list hd.call_context) *)
   (* | hd1 :: hd2 :: [] -> *)
   (*   let call_context = convert_ctxt_list hd1.call_context in *)
   (*   assert (call_context = (convert_ctxt_list hd2.call_context)); *)
   (*   call_context *)
   (* | _ -> failwith "More than two tip alternative tipcalls are not supported.") *)

let strip_context call =
  (* TODO: why do we erase the return value? *)
  {call with ret = None; call_context = []; ret_context = [];}

(* Returns the segment and whether it is a part of an iteration or not*)
let get_relevant_segment pref boundary_fun eventproc_iteration_begin =
  let rec last_relevant_seg hist candidate =
    match hist with
    | c :: rest ->
      if (String.equal c.fun_name eventproc_iteration_begin) then
        let (seg,_) = last_relevant_seg rest hist in
        (seg, true)
      else if (String.equal c.fun_name boundary_fun) then
        last_relevant_seg rest hist
      else
        last_relevant_seg rest candidate
    | [] -> (candidate, false)
  in
  match pref.tip_calls with
  | [] -> failwith "must have at least one tip call."
  | hd :: _ ->
    if (String.equal hd.fun_name boundary_fun) ||
       (String.equal hd.fun_name eventproc_iteration_begin) then
      ({history=[]; tip_calls = List.map pref.tip_calls ~f:strip_context},
       false)
    else
      match last_relevant_seg pref.history [] with
      | (bnd :: rest, inside_iteration) ->
        ({history = strip_context bnd :: rest; tip_calls = pref.tip_calls},
         inside_iteration)
      | ([], _) -> (pref, false)

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

let allocate_dummy addr t =
  let name = ("dummy_" ^ (Int64.to_string addr)) in
  allocated_dummies := {vname=name; t={w=Noidea;
                                       s=Noidea;
                                       precise=t}}::!allocated_dummies;
  known_addresses :=
    Int64.Map.add !known_addresses
      ~key:addr ~data:[{value={v=Id name;t}; callid=0; str_depth=0; tt=t}];
  {v=Id name;t}

let fixup_placeholder_ptrs_in_tterm tterm =
  let replace_placeholder = function
    | {v=Utility (Ptr_placeholder addr); t=Ptr ptee_t} ->
      lprintf "fixing placeholder for %Ld\n" addr;
      begin match ptee_t, find_first_known_address addr ptee_t with
        | Unknown, _ -> failwith ("Unresolved placeholder of unknown type:" ^
                                  (render_tterm tterm))
        | _, Some x -> Some x
        | _, None -> let dummy_value = allocate_dummy addr ptee_t in
          Some {v=Addr dummy_value; t=Ptr ptee_t}
      end
    | {v=Utility _;t} ->
      failwith ("Ptr placeholder type is not a pointer:" ^
                (render_tterm tterm) ^ " : " ^ (ttype_to_str t))
    | _ -> None
  in
  call_recursively_on_tterm replace_placeholder tterm

let fixup_placeholder_ptrs vars =
  List.map vars ~f:(fun {name;value} ->
    {name;value=fixup_placeholder_ptrs_in_tterm value})

let fixup_placeholder_ptrs_in_eq_cond {lhs;rhs} =
  lprintf "fixing pph in %s == %s\n" (render_tterm lhs) (render_tterm rhs);
  match rhs.v with
  | Utility (Ptr_placeholder addr) ->
    begin match find_first_known_address addr rhs.t with
      | Some x -> {lhs=lhs; rhs=x}
      | None ->
        known_addresses :=
          Int64.Map.add !known_addresses
            ~key:addr ~data:[{value=lhs; callid=0; str_depth=0; tt=rhs.t}];
        {lhs=lhs;rhs=lhs}
    end
  | _ ->
    {lhs=fixup_placeholder_ptrs_in_tterm lhs;
     rhs=fixup_placeholder_ptrs_in_tterm rhs}

let fixup_placeholder_ptrs_in_hist_calls hist_calls =
  let in_one_call {context;result} =
    {context;result=
               {args_post_conditions=List.map result.args_post_conditions
                    ~f:fixup_placeholder_ptrs_in_eq_cond;
                ret_val=fixup_placeholder_ptrs_in_tterm result.ret_val}}
  in
  List.map hist_calls ~f:in_one_call

let fixup_placeholder_ptrs_in_tip_call tip_call =
  let in_one_result {args_post_conditions;ret_val;post_statements} =
    {args_post_conditions = List.map args_post_conditions
         ~f:fixup_placeholder_ptrs_in_eq_cond;
     ret_val = fixup_placeholder_ptrs_in_tterm ret_val;
     post_statements = List.map post_statements
         ~f:fixup_placeholder_ptrs_in_tterm}
  in
  {tip_call with results = List.map tip_call.results
                     ~f:in_one_result}

let guess_dynamic_types basic_ftype_of pref =
  let type_match t arg =
    match t, arg with
    | Ptr (Str (_, fields)), {aname=_; value=_; ptr=Curioptr ptee}
      when List.length fields = List.length ptee.before.break_down ->
      List.for_all2_exn fields ptee.before.break_down
        ~f:(fun (name,t) {fname;value;addr=_} ->
            String.equal name fname
            (* One level introspection should be enough *))
    | _ -> false
  in
  List.fold (pref.history @ pref.tip_calls)
    ~init:(Int.Map.empty:int Int.Map.t Int.Map.t) ~f:(fun acc call ->
        let arg_types = (basic_ftype_of call.fun_name).arg_types in
        let fun_map =
        List.foldi (List.zip_exn call.args arg_types) ~init:Int.Map.empty
          ~f:(fun (n:int) (acc:int Int.Map.t) ((arg:Trace_prefix.arg), (t:arg_type)) ->
              match t with
              | Static _ -> acc
              | Dynamic ts ->
                  match List.findi ts ~f:(fun _ t -> type_match t arg) with
                    | Some (num, tt) -> lprintf "guessed %s(%d) for %s/%d#%d\n"
                                          (ttype_to_str tt) num
                                          call.fun_name call.id n;
                      Int.Map.add acc ~key:n ~data:num
                  | None -> failwith
                              ("Can not guess a dynamic type for " ^
                               call.fun_name ^ "/" ^ Int.to_string call.id ^
                               " argument # " ^
                               Int.to_string n))
        in
        if Int.Map.is_empty fun_map then acc
        else Int.Map.add acc ~key:call.id ~data:fun_map)

let build_ir fun_types fin preamble boundary_fun finishing_fun
  eventproc_iteration_begin eventproc_iteration_end =
  let ftype_of fun_name =
    match String.Map.find fun_types fun_name with
    | Some spec -> spec
    | None -> failwith ("unknown function " ^ fun_name)
  in
  let (pref,inside_iteration) = get_relevant_segment
      (Trace_prefix.trace_prefix_of_sexp (Sexp.load_sexp fin))
      boundary_fun eventproc_iteration_begin
  in
  lprintf "inside_iteration: %s\n" (if inside_iteration then "true" else "false");
  let pref = distribute_ids pref in
  let guessed_dyn_types = guess_dynamic_types ftype_of pref in
  let ftype_of = (ftype_of,guessed_dyn_types) in
  let finishing_iteration =
    is_the_last_function_finishing pref eventproc_iteration_end
  in
  let finishing =
    (is_the_last_function_finishing pref finishing_fun) ||
    finishing_iteration
  in
  let preamble = preamble in
  let export_point = "export_point" in
  let free_vars = get_basic_vars ftype_of pref in
  let free_vars = typed_vars_to_varspec free_vars in
  let arguments = allocate_args ftype_of pref (name_gen "arg") in
  let arguments = (allocate_extra_ptrs ftype_of pref)@arguments in
  let rets = allocate_rets ftype_of pref in
  (* let (rets, tip_dummies) = allocate_tip_ret_dummies ftype_of pref.tip_calls rets in *)
  let (hist_calls,tip_call) = extract_calls_info ftype_of pref rets free_vars in
  let context_assumptions = collect_context pref in
  let cmplxs = !allocated_complex_vals in
  let hist_calls = fixup_placeholder_ptrs_in_hist_calls hist_calls in
  let tip_call = fixup_placeholder_ptrs_in_tip_call tip_call in
  let arguments = fixup_placeholder_ptrs arguments in
  let tmps = !allocated_tmp_vals in
  (* Do not render the allocated_dummies *)
  {preamble;free_vars;arguments;tmps;
   cmplxs;context_assumptions;hist_calls;tip_call;
   export_point;finishing;
   complete_event_loop_iteration = inside_iteration && finishing_iteration;
   semantic_checks=""}
