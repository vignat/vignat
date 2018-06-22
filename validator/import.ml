open Core
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

type t_width = W1 | W8 | W16 | W32 | W64
type t_sign = Sgn | Unsgn
type type_guess = {w:t_width confidence;
                   s:t_sign confidence;
                   precise: ttype}

type typed_var = {vname:string; t: type_guess;}

type moment = Beginning | After of int

type address_spec = {value:tterm;
                     callid:moment;
                     str_depth:int;
                     tt:ttype;
                     breakdown:int64 String.Map.t}

type guessed_types = {ret_type: ttype;
                      arg_types: ttype list;
                      extra_ptr_types: ttype String.Map.t}

let known_addresses : address_spec list Int64.Map.t ref = ref Int64.Map.empty


let ttype_of_guess = function
  | {precise=Unknown;s=Tentative Sgn;w;}
  | {precise=Unknown;s=Sure Sgn;w;} -> begin match w with
      | Noidea -> Sunknown
      | Sure W1 | Tentative W1 -> Boolean
      | Sure W8 | Tentative W8 -> Sint8
      | Sure W16 | Tentative W16 -> Sint16
      | Sure W32 | Tentative W32 -> Sint32
      | Sure W64 | Tentative W64 -> Sint64
      end
  | {precise=Unknown;s=Tentative Unsgn;w;}
  | {precise=Unknown;s=Sure Unsgn;w;} -> begin match w with
      | Noidea -> Uunknown
      | Sure W1 | Tentative W1 -> Boolean
      | Sure W8 | Tentative W8 -> Uint8
      | Sure W16 | Tentative W16 -> Uint16
      | Sure W32 | Tentative W32 -> Uint32
      | Sure W64 | Tentative W64 -> Uint64
      end
  | {precise=Unknown;s=Noidea;w=Sure W1;}
  | {precise=Unknown;s=Noidea;w=Tentative W1;} -> Boolean
  | {precise=Unknown;s=Noidea;w=_;} -> Unknown
  | {precise;s=_;w=_} -> precise

(* TODO: elaborate. *)
let guess_type exp t =
  match t with
  | Uunknown -> begin match exp with
      | Sexp.List [Sexp.Atom w; _] when w = "w8" -> Uint8
      | Sexp.List [Sexp.Atom w; _] when w = "w16" -> Uint16
      | Sexp.List [Sexp.Atom w; _] when w = "w32" -> Uint32
      | Sexp.List [Sexp.Atom w; _] when w = "w64" -> Uint64
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "And") && (String.equal w "w32") -> Uint32
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "Concat") && (String.equal w "w32") -> Uint32
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "Concat") && (String.equal w "w64") -> Uint64
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "Read") && (String.equal w "w8") -> Uint8
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ReadLSB") && (String.equal w "w16") -> Uint16
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ReadLSB") && (String.equal w "w32") -> Uint32
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ReadLSB") && (String.equal w "w64") -> Uint64
      | _ -> failwith ("GUESS TYPE FAILURE UUnknown " ^ (Sexp.to_string exp))
    end
  | Sunknown -> begin match exp with
      | Sexp.List [Sexp.Atom w; _] when w = "w8" -> Sint8
      | Sexp.List [Sexp.Atom w; _] when w = "w16" -> Sint16
      | Sexp.List [Sexp.Atom w; _] when w = "w32" -> Sint32
      | Sexp.List [Sexp.Atom w; _] when w = "w64" -> Sint64
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ZExt") && (String.equal w "w32") -> Sint32
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "Concat") && (String.equal w "w32") -> Sint32
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "Read") && (String.equal w "w8") -> Sint8
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ReadLSB") && (String.equal w "w16") -> Sint16
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ReadLSB") && (String.equal w "w32") -> Sint32
      | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
        when (String.equal f "ReadLSB") && (String.equal w "w64") -> Sint64
      | _ -> failwith ("GUESS TYPE FAILURE SUnknown " ^ (Sexp.to_string exp))
    end
  | Unknown ->  begin match exp with
    | Sexp.Atom f when f = "false" || f = "true" -> Boolean
    | Sexp.List [Sexp.Atom w; Sexp.Atom f] when w = "w32" && f = "0" -> lprintf "GUESS TYPE BOOL\n"; Boolean
    | Sexp.List [Sexp.Atom w; _] when w = "w8" -> Uint8
    | Sexp.List [Sexp.Atom w; _] when w = "w16" -> Uint16
    | Sexp.List [Sexp.Atom w; _] when w = "w32" -> Uint32
    | Sexp.List [Sexp.Atom w; _] when w = "w64" -> Uint64
    | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
      when (String.equal f "Read") && (String.equal w "w8") -> Uint8
    | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
      when (String.equal f "ReadLSB") && (String.equal w "w16") -> Uint16
    | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
      when (String.equal f "ReadLSB") && (String.equal w "w32") -> Uint32
    | Sexp.List ((Sexp.Atom f) :: (Sexp.Atom w) :: _)
      when (String.equal f "ReadLSB") && (String.equal w "w64") -> Uint64
    | _ -> lprintf "GUESS TYPE UNKNOWN\n"; Uint64
    end
  | _  -> t

let int64_of_sexp value =
  let str = Sexp.to_string value in
  let prefix = String.sub str ~pos:0 ~len:5 in
  assert(prefix = "(w64 ");
  Int64.of_string (String.sub str ~pos:5 ~len:((String.length str) - 6)) (* -5 for begining -1 for end paren *)

(* TODO: this should spit out a type to help the validator *)
let int_str_of_sexp value =
  let str = Sexp.to_string value in
  let prefix = String.sub str ~pos:0 ~len:3 in
  if prefix = "(w8" then
    String.sub str ~pos:4 ~len:((String.length str - 5))
  else if prefix = "(w1" || prefix = "(w3" || prefix = "(w6" then (* 16, 32, 64 *)
    String.sub str ~pos:5 ~len:((String.length str - 6))
  else str

let infer_type_sign f =
  if String.equal f "Sle" then Sure Sgn
  else if String.equal f "Slt" then Sure Sgn
  else if String.equal f "Ule" then Sure Unsgn
  else if String.equal f "Ult" then Sure Unsgn
  else if String.equal f "Eq" then Sure Unsgn
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
        merge_defs (get_defs def) (String.Map.add_exn (do_list tl)
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
                                 ~f:(fun (name,(new_el,_)) -> (name,new_el)))
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
    Map.iteri (get_defs sexp) ~f:(fun ~key ~data ->
        lprintf "%s ::: %s\n" key (Sexp.to_string data));
    lprintf "expanded defs: ";
    Map.iteri defs ~f:(fun ~key ~data ->
        lprintf "%s ::: %s\n" key (Sexp.to_string data));
    failwith ("incomplete map expansion for " ^ (Sexp.to_string sexp));
  end;
  (fst (expand_exp (remove_defs sexp) defs))

let get_fun_arg_type (_,type_guesses) (call : Trace_prefix.call_node) arg_num =
  List.nth_exn (Int.Map.find_exn type_guesses call.id).arg_types arg_num

let get_fun_extra_ptr_type
    (_,type_guesses)
    (call : Trace_prefix.call_node)
    exptr_name =
  String.Map.find_exn
    (Int.Map.find_exn type_guesses call.id).extra_ptr_types
    exptr_name

let get_fun_ret_type (_, type_guesses) call_id =
  (Int.Map.find_exn type_guesses call_id).ret_type

let get_num_args ((ftype_of:string->fun_spec), _) call =
  List.length (ftype_of call.fun_name).arg_types

let to_symbol str =
  let no_spaces = String.substr_replace_all str ~pattern:" " ~with_:"_" in
  let no_octotorps = String.substr_replace_all no_spaces ~pattern:"#" ~with_:"num" in
  no_octotorps

let get_var_name_of_sexp exp =
  match exp with
  | Sexp.List [Sexp.Atom rd; Sexp.Atom _; Sexp.List [Sexp.Atom _; Sexp.Atom pos]; Sexp.Atom name]
    when ( String.equal rd "ReadLSB" ||
           String.equal rd "Read") -> Some (to_symbol name ^ "_" ^ pos)
  | _ -> None

let get_read_width_of_sexp exp =
  match exp with
  | Sexp.List [Sexp.Atom rd; Sexp.Atom w; Sexp.List _; Sexp.Atom _]
    when (String.equal rd "ReadLSB" ||
          String.equal rd "Read") -> Some w
  | _ -> None

let sexp_is_of_this_width sexp w =
  match get_read_width_of_sexp sexp with
  | Some ww -> String.equal ww w
  | _ -> false

let rec canonicalize_sexp sexp =
  match expand_shorted_sexp sexp with
  | Sexp.List [Sexp.Atom "Extract"; Sexp.Atom w; Sexp.Atom "0";
               Sexp.List [Sexp.Atom "ZExt"; Sexp.Atom _; arg];]
    when sexp_is_of_this_width arg w ->
    lprintf "canonicalized: %s\n" (Sexp.to_string arg);
    (* TODO: make sure no sign-magic breaks here *)
    canonicalize_sexp arg
  | Sexp.List (Sexp.Atom f :: args) -> Sexp.List (Sexp.Atom f :: List.map args ~f:canonicalize_sexp)
  | _ -> sexp

let map_set_n_update_alist mp lst =
  List.fold lst ~init:mp ~f:(fun acc (key,data) -> String.Map.set acc ~key ~data)

let parse_int str =
  (* As a hack: handle -10 in 64bits.
     TODO: handle more generally*)
  if (String.equal str "18446744073709551606") then Some (-10)
  (* As another hack: handle -300 in 64bits. *)
  else if (String.equal str "18446744073709551316") then Some (-300)
  else
    try Some (int_of_string str)
    with _ -> None

let is_int str = match parse_int str with Some _ -> true | None -> false

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
    | Sunknown | Uunknown -> failwith "s/uunknown..." (*if given.t = Unknown then known.t else given.t*)
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

let convert_str_to_width_confidence w =
  if String.equal w "w1" then Sure W1
  else if String.equal w "w8" then Sure W8
  else if String.equal w "w16" then Sure W16
  else if String.equal w "w32" then Sure W32
  else if String.equal w "w64" then Sure W64
  else Noidea

let is_bool_fun fname =
  if String.equal fname "Eq" then true
  else if String.equal fname "Sle" then true
  else if String.equal fname "Slt" then true
  else if String.equal fname "Ule" then true
  else if String.equal fname "Ult" then true
  else false

(* TODO this is crazy, we parse a bunch of sexps and give the proper types in another method and here we redo the whole work *)
let rec get_var_decls_of_sexp exp guess (known_vars:typed_var String.Map.t) : typed_var list =
  match get_var_name_of_sexp exp, get_read_width_of_sexp exp with
  | Some name, Some w ->
    let precise = ttype_of_guess {guess with w = convert_str_to_width_confidence w} in
    begin match String.Map.find known_vars name with
      | Some spec -> [update_var_spec spec {precise;s=guess.s;w=convert_str_to_width_confidence w}]
      | None -> [{vname = name; t={precise;s=guess.s;w=convert_str_to_width_confidence w}}]
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
      when (String.equal w "w64") || (String.equal w "w32") || (String.equal w "w16") || (String.equal w "w8") ->
      let wi = convert_str_to_width_confidence w in
      if String.equal f "ZExt" then
        match tl with
        | [tl] -> get_var_decls_of_sexp
                    tl {s=(Sure Unsgn);w=Noidea;precise=Unknown} known_vars
        | _ ->
          lprintf "ZExt may have only one argument: %s\n" (Sexp.to_string exp);
          failwith "ZExt may have only one argument (besides w..)."
      else
        let si = choose_guess (infer_type_sign f) guess.s in
        (List.join (List.map tl ~f:(fun e ->
             get_var_decls_of_sexp e {s=si;w=wi;precise=guess.precise} known_vars)))
    | Sexp.List (Sexp.Atom f :: tl) when f <> "w8" && f <> "w16" && f <> "w32" && f <> "w64" ->
      let si = choose_guess (infer_type_sign f)
          (choose_guess (guess_sign_l tl known_vars) guess.s)
      in
      List.join (List.map tl ~f:(fun e -> get_var_decls_of_sexp e {s=si;w=Noidea;precise=guess.precise} known_vars))
    | _ -> []
    end
  | _,_ -> failwith ("inconsistency in get_var_name/get_read_width: " ^ (Sexp.to_string exp))

let make_name_alist_from_var_decls (lst: typed_var list) =
  List.map lst ~f:(fun x -> (x.vname,x))

let get_vars_from_plain_val v type_guess known_vars =
  (*TODO: proper type induction here, e.g. Sadd w16 -> Sint16, ....*)
  let decls = get_var_decls_of_sexp (canonicalize_sexp v) type_guess known_vars in
  map_set_n_update_alist known_vars (make_name_alist_from_var_decls decls)

let type_guess_of_ttype t = match t with
  | Sint64 -> {s=Sure Sgn;w=Sure W64;precise=t}
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
let allocated_dummies = ref []

let get_sint_in_bounds v =
  (*Special case for 64bit -10, for now,
    FIXME: make a more general case.*)
  if (String.equal v "18446744073709551606") then -10
  (* also -300 *)
  else if (String.equal v "18446744073709551316") then -300
  else
    let integer_val = Int.of_string v in
    if Int.(integer_val > 2147483647) then
      integer_val - 2*2147483648
    else
      integer_val

let make_cmplx_val exp t =
  let key = int_str_of_sexp exp in
  match String.Map.find !allocated_complex_vals key with
  | Some spec -> {v=Id spec.name;t=spec.value.t}
  | None ->
    let name = complex_val_name_gen#generate in
    lprintf "CMPLX NAME: %s SEXP: %s TYPE: %s\n" name (Sexp.to_string exp) (ttype_to_str t);
    let value = {v=Id key;t} in
    allocated_complex_vals :=
      String.Map.add_exn !allocated_complex_vals ~key
        ~data:{name;value};
    {v=Id name;t}

(*TODO: rewrite this in terms of my IR instead of raw Sexps*)
let eliminate_false_eq_0 exp t =
  match (exp,t) with
  | Sexp.List [Sexp.Atom eq1; Sexp.Atom fls;
               Sexp.List [Sexp.Atom eq2; Sexp.List [Sexp.Atom _; Sexp.Atom zero]; e]],
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


let rec guess_type_l exps t =
  match exps with
  | hd :: tl -> begin match guess_type hd t with
      | Unknown | Sunknown | Uunknown -> guess_type_l tl t
      | s -> s
    end
  | [] -> Unknown

let find_first_known_address_comply addr tt at property =
  let legit_candidates lst =
    List.filter lst ~f:(fun x ->
        (match x.callid, at with
         | Beginning, _ -> true
         | After _, Beginning -> false
         | After id, After searched_for -> id <= searched_for)
        &&
        (match x.tt, tt with
         | _, Unknown
         | _, Void ->
         (* TODO: should not really occur.
                         but left here for the sake of void** output pointers,
                         that are not concretized yet. *)
          failwith ("Searching for a void instantiation of addr" ^
                  (Int64.to_string addr) ^ " x.tt:" ^ (ttype_to_str x.tt) ^ " tt:" ^ (ttype_to_str tt))
         | t1, t2 ->
           if (t1 <> t2) then
             lprintf "discarding: %s != %s\n"
               (ttype_to_str t1) (ttype_to_str t2);
           t1 = t2)
        &&
        (property x))
  in
  let find_the_right candidates =
    List.reduce ~f:(fun prev cand ->
        match prev.callid, cand.callid with
        | Beginning, _ -> prev
        | _, Beginning -> cand
        | After x1, After x2 ->
          if x1 < x2 then prev
          else if x2 < x1 then cand
          else if prev.str_depth < cand.str_depth then prev
          else cand)
      candidates
  in
  Option.bind (Int64.Map.find !known_addresses addr)
    ~f:(fun lst ->
       Option.map ~f:(fun addr_sp -> addr_sp.value)
         (find_the_right (legit_candidates lst)))

let moment_to_str = function
  | Beginning -> "<|"
  | After x -> ("> " ^ (string_of_int x))

let find_first_known_address addr tt at =
  lprintf "looking for first %Ld : %s at %s\n" addr (ttype_to_str tt) (moment_to_str at);
  find_first_known_address_comply addr tt at (fun _ -> true)

let rec printable_tterm cand =
  lprintf "checking for printability: %s\n" (render_tterm cand);
  match cand with
  | {v=Addr x;t=_} -> printable_tterm x
  | {v=Id _;t=_} -> true
  | {v=Str_idx (x,_);t=_} -> printable_tterm x
  | {v=Deref x;t=_} -> printable_tterm x
  | _ -> lprintf "nope\n";
    false

let find_first_symbol_by_address addr tt at =
  lprintf "looking for a first symbol at *%Ld : %s at %s\n"
    addr (ttype_to_str tt) (moment_to_str at);
  find_first_known_address_comply addr tt at
    (fun candidate -> printable_tterm candidate.value)

let find_first_known_address_or_dummy addr t at =
  match find_first_known_address addr t at with
  | Some tt -> tt
  | None -> {v=Utility (Ptr_placeholder addr); t=Ptr t}

let rec get_sexp_value exp ?(at=Beginning) t =
  let exp = canonicalize_sexp exp in
  let exp = eliminate_false_eq_0 exp t in
  let t = match t with
    |Unknown|Sunknown|Uunknown -> guess_type exp t
    |_ -> t
  in
  let exp = match exp with
    | Sexp.List [Sexp.Atom w; Sexp.Atom f] when w = "w8" || w = "w16" || w = "w32" || w = "w64" -> Sexp.Atom f
    | _ -> exp
  in
  match exp with
  | Sexp.Atom v ->
    begin
      match t with
      | Sint64 | Sint32 | Sint16 | Sint8 -> {v=Int (get_sint_in_bounds v);t}
      | _ ->
        if String.equal v "true" then {v=Bool true;t=Boolean}
        else if String.equal v "false" then {v=Bool false;t=Boolean}
        (*FIXME: deduce the true integer type for the value: *)
        else begin match parse_int v with
          | Some n -> let addr = (Int64.of_int n) in
                      if addr = 0L then {v=Int 0; t}
                      else
                        begin match t with
                        | Ptr x -> find_first_known_address_or_dummy addr x at
                        | _ -> {v=Int n;t} end
          | None -> {v=Id v;t} end
    end
  | Sexp.List [Sexp.Atom f; Sexp.Atom w; Sexp.Atom offset; src;]
    when (String.equal f "Extract") && (String.equal offset "0") ->
    (*FIXME: make sure the typetransformation works.*)
    (*FIXME: pass a right type to get_sexp_value here*)
    if (String.equal w "w32") then
      get_sexp_value src t ~at
    else if (String.equal w "w64") then
      get_sexp_value src t ~at (*failwith "get_sexp_value extract w64 not supported"*)
    else
      {v=Cast (t, get_sexp_value src Sint32 ~at);t}
  | Sexp.List [Sexp.Atom f; Sexp.Atom offset; src;]
    when (String.equal f "Extract") && (String.equal offset "0") ->
    get_sexp_value src Boolean ~at
  | Sexp.List [Sexp.Atom f; Sexp.Atom w; arg]
    when (String.equal f "SExt") && (String.equal w "w64") ->
    get_sexp_value arg t ~at (*TODO: make sure this ignorance is ok *)
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "Add") ->
    begin (* Prefer a variable in the left position
             due to the weird VeriFast type inference rules.*)
      match lhs with
      | Sexp.Atom str ->
        begin match parse_int str with
        | Some n -> {v=Bop (Sub,(get_sexp_value rhs t ~at),{v=(Int n);t});t}
        | _ -> {v=Bop (Add,(get_sexp_value lhs t ~at),(get_sexp_value rhs t ~at));t} end
      | _ -> {v=Bop (Add,(get_sexp_value lhs t ~at),(get_sexp_value rhs t ~at));t}
    end
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Slt") ->
    (*FIXME: get the actual type*)
    let ty = guess_type_l [lhs;rhs] Sunknown in
    {v=Bop (Lt,(get_sexp_value lhs ty ~at),(get_sexp_value rhs ty ~at));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Sle") ->
    (*FIXME: get the actual type*)
    {v=Bop (Le,(get_sexp_value lhs Sunknown ~at),(get_sexp_value rhs Sunknown ~at));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Ule") ->
    (*FIXME: get the actual type*)
    {v=Bop (Le,(get_sexp_value lhs Uunknown ~at),(get_sexp_value rhs Uunknown ~at));t}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Ult") ->
    {v=Bop (Lt,(get_sexp_value lhs Uunknown ~at),(get_sexp_value rhs Uunknown ~at));t}
  | Sexp.List [Sexp.Atom "Eq"; Sexp.List [Sexp.Atom "w32"; Sexp.Atom "0"]; Sexp.List ((Sexp.Atom "ReadLSB" :: tl))] ->
    {v=Bop (Eq, {v=Int 0;t=Uint32}, (get_sexp_value (Sexp.List (Sexp.Atom "ReadLSB" :: tl)) Uint32 ~at));t=Boolean}
  | Sexp.List [Sexp.Atom f; lhs; rhs]
    when (String.equal f "Eq") ->
    let ty = guess_type_l [lhs;rhs] Unknown in
    {v=Bop (Eq,(get_sexp_value lhs ty ~at),(get_sexp_value rhs ty ~at));t}
  | Sexp.List [Sexp.Atom f; _; e]
    when String.equal f "ZExt" ->
    (*TODO: something smarter here.*)
    get_sexp_value e t ~at
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "And") &&
         ((is_bool_expr lhs) || (is_bool_expr rhs)) ->
    (*FIXME: and here, but really that is a bool expression, I know it*)
    (*TODO: check t is really Boolean here*)
    {v=Bop (And,(get_sexp_value lhs Boolean ~at),(get_sexp_value rhs Boolean ~at));t}
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; lhs; rhs]
    when (String.equal f "And") ->
    begin 
      match rhs with
      | Sexp.List [Sexp.Atom "w32"; Sexp.Atom n] when is_int n ->
        if t = Boolean then
          {v=Bop (Eq, (get_sexp_value rhs Uint32 ~at), {v=Bop (Bit_and,(get_sexp_value lhs Uint32 ~at),(get_sexp_value rhs Uint32 ~at));t=Uint32});t=Boolean}
        else
          {v=Bop (Bit_and,(get_sexp_value lhs Uint32 ~at),(get_sexp_value rhs Uint32 ~at));t=Uint32}
      | _ ->
        let ty = guess_type_l [lhs;rhs] t in
        lprintf "interesting And case{%s}: %s "
          (ttype_to_str ty) (Sexp.to_string exp);
        if ty = Boolean then
          {v=Bop (And,(get_sexp_value lhs ty ~at),(get_sexp_value rhs ty ~at));t=ty}
        else
          {v=Bop (Bit_and,(get_sexp_value lhs ty ~at),(get_sexp_value rhs ty ~at));t=ty}
    end
  | Sexp.List [Sexp.Atom f; Sexp.Atom _; Sexp.Atom lhs; rhs;]
    when (String.equal f "Concat") && (String.equal lhs "0") ->
    get_sexp_value rhs t ~at
  | Sexp.List [Sexp.Atom "Select"; Sexp.Atom _; nested; Sexp.List [Sexp.Atom _; Sexp.Atom "1"]; Sexp.List [Sexp.Atom _; Sexp.Atom "0"]] ->
    (* This is equivalent to x ? 1 : 0 ==> we just pretend x is a boolean *)
    get_sexp_value nested Boolean ~at
  | _ ->
    begin match get_var_name_of_sexp exp with
      | Some name -> {v=Id name;t}
      | None ->
        make_cmplx_val exp t
    end

let rec get_struct_val_value valu t =
  match t, valu.full with
  | Str (strname, fields), _ ->
    begin
    (*   match get_var_name_of_sexp valu.full with *)
    (* | Some name -> {v=Id name;t} *)
    (* | None -> <^^^ this was working a while ago, may be it should be
       left somewhere *)
      lprintf "GSVV Destruct: %s; Need %d fields got %d fields (%s).\n" strname
        (List.length fields) (List.length valu.break_down)
        (match valu.sname with | Some x -> x | None -> "?");
      if List.length valu.break_down <>
         List.length fields then begin
        lprintf "GSVV %s expects %d fields but found only %d"
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
  (*| Ptr ptee, None -> failwith ("GSVV given a pointer! " ^ (ttype_to_str ptee))*)
  | _, Some v -> lprintf "GSVV using sexp for type %s\n" (ttype_to_str t); get_sexp_value v t
  | _, None -> lprintf "GSVV undef for type %s\n" (ttype_to_str t); {t;v=Undef}

let update_ptee_variants nval older =
  match nval with
  | {value={t=Unknown;v=_};_} -> older
  | _ ->
    match older with
    | [{value={t=Unknown;v=_};_}] -> [nval]
    | _ -> nval::older

(* Takes a pointer, records it into known_addresses *)
let rec add_to_known_addresses
    (base_value: tterm) breakdown addr
    callid depth =
  (*lprintf "ATK %s : %s at %s\n" (render_tterm base_value) (ttype_to_str base_value.t) (moment_to_str callid);*)
  begin match base_value.t with
  | Ptr (Str (_,fields) as ptee_type) ->
    let fields = List.fold fields ~init:String.Map.empty
        ~f:(fun fields (name,t) ->
            String.Map.add_exn fields ~key:name ~data:t)
    in
    List.iter breakdown ~f:(fun {fname;value;addr} ->
        let ftype = match String.Map.find fields fname with
          | Some t -> t | None -> failwith ("Unknown field type for " ^ fname)
        in
        let b_value = {t=Ptr ftype;
                       v=Addr {t=ftype;
                               v=Str_idx ({t=ptee_type;
                                           v=Deref base_value},fname)}}
        in
        add_to_known_addresses
          b_value value.break_down
          addr callid (depth+1);)
  | _ ->
    assert((List.length breakdown) = 0)
  end;
  lprintf "allocating *%Ld = %s : %s at %s\n"
    addr
    (render_tterm base_value)
    (ttype_to_str base_value.t)
    (moment_to_str callid);
  let prev = match Int64.Map.find !known_addresses addr with
    | Some value -> value
    | None -> []
  in
  let breakdown =
    List.fold breakdown ~init:String.Map.empty
      ~f:(fun acc {fname;value=_;addr} ->
          String.Map.add_exn acc ~key:fname ~data:addr)
  in
  known_addresses := Int64.Map.set !known_addresses
      ~key:addr ~data:(update_ptee_variants
                         {value=base_value;
                          callid;
                          str_depth=depth;
                          tt=base_value.t;
                          breakdown}
                         prev)
(* Takes a symbolic expression and records
   it as a pointee into known_addresses*)
let rec add_known_symbol_at_address (value: tterm) addr callid depth =
  let prev = match Int64.Map.find !known_addresses addr with
    | Some v -> v
    | None -> []
  in
  let find_field_addr strname fieldname fieldtype =
    List.find_map prev ~f:(fun aspec ->
        lprintf "find_field_addr %s %s(%s) -> %Ld considering aspec: %s : %s\n"
          strname fieldname (ttype_to_str fieldtype) addr (render_tterm aspec.value) (ttype_to_str aspec.tt);
        match aspec.tt with
        | Ptr (Str (aspecname, _)) when aspecname = strname -> lprintf "YES %d\n" (String.Map.length aspec.breakdown);
          String.Map.find aspec.breakdown fieldname
        | _ -> None)
  in
  begin match value.t with
  | Ptr (Str (strname,fields)) ->
    List.iter fields ~f:(fun (fname,ftype) ->
        lprintf "for %s.%s : %s\n" strname fname (ttype_to_str ftype);
        begin match find_field_addr strname fname ftype with
        | Some fa -> add_known_symbol_at_address
                     {v=Addr {v=Str_idx ({v=Deref value; t=Str (strname,fields)}, fname);
                              t=ftype};
                      t=Ptr ftype}
                     fa callid (depth + 1)
        | None -> failwith ("failed to find field " ^ fname ^ " at the address " ^ (Int64.to_string addr))
        end)
  | Str (strname,fields) ->
    List.iter fields ~f:(fun (fname,ftype) ->
        let field_addr = match find_field_addr strname fname ftype with
          | Some fa -> fa
          | None -> failwith ("failed to find field " ^ fname ^
                              " at the address " ^ (Int64.to_string addr))
        in
        add_known_symbol_at_address
          {v=Addr {v=Str_idx (value, fname); t=ftype}; t=Ptr ftype}
          field_addr callid (depth + 1))
  | Ptr (Ptr ptee) ->
    List.iter prev ~f:(fun aspec ->
        match (simplify_tterm aspec.value).v with
        | Addr {v=Utility (Ptr_placeholder addr);t=_} ->
          add_known_symbol_at_address {v=Deref value;
                                       t=Ptr ptee}
            addr callid (depth + 1)
        | _ -> ())
  | _ -> ()
  end;
  add_to_known_addresses (simplify_tterm value) [] addr callid depth

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
    lprintf "getting_vars from %s\n" call.fun_name;
    if (List.length call.args <> get_num_args ftype_of call) then
      failwith ("Wrong number of arguments in the plugin for function " ^
                call.fun_name);
    let arg_vars = List.foldi call.args ~init:known_vars
        ~f:(fun i acc arg ->
            let arg_type = get_fun_arg_type ftype_of call i in
            complex_value_vars arg.value arg.ptr arg_type false acc)
    in
    let extra_ptr_vars = List.fold call.extra_ptrs ~init:arg_vars
        ~f:(fun acc {pname;value=_;ptee} ->
            let ptee_type =
              (get_pointee (get_fun_extra_ptr_type ftype_of call pname)) in
          get_extra_ptr_pointee_vars ptee ptee_type acc)
    in
    let ret_vars = match call.ret with
      | Some ret ->
        complex_value_vars
          ret.value ret.ptr
          (get_fun_ret_type ftype_of call.id) true extra_ptr_vars
      | None -> extra_ptr_vars in
    let add_vars_from_ctxt vars ctxt =
      map_set_n_update_alist vars
        (make_name_alist_from_var_decls
           (get_var_decls_of_sexp
              (canonicalize_sexp ctxt)
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

let allocate_rets ftype_of tpref =
  let alloc_call_ret acc_rets call =
    let ret_type = get_fun_ret_type ftype_of call.id in
    match call.ret with
    | Some {value;ptr;} ->
      let name = "ret"^(Int.to_string call.id) in
      let data = match ptr with
        | Nonptr -> {name;value=get_sexp_value value ret_type}
        | Funptr _ -> failwith "TODO:support funptr retuns."
        | Apathptr ->
          let addr = int64_of_sexp value in
          if (addr = 0L) then
            {name;value={t=ret_type;v=Zeroptr}}
          else begin
            add_to_known_addresses {t=ret_type;v=Id name} [] addr (After call.id) 0;
            {name;value={t=ret_type;v=Addr {t=get_pointee ret_type;v=Undef}}}
          end
        | Curioptr ptee ->
          let addr = int64_of_sexp value in
          add_to_known_addresses {v=Id name;t=ret_type}
            ptee.after.break_down addr (After call.id) 0;
          {name;value={t=ret_type;v=Addr (get_struct_val_value
                                            ptee.after (get_pointee ret_type))}}
      in
      Int.Map.add_exn acc_rets ~key:call.id ~data
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
          match Int.Map.add rets ~key:call.id ~data:{ret with name="tip_ret"}
          with
          | `Ok new_map -> new_map
          | `Duplicate -> rets (* nevermind *))

let moment_before call_id =
  if 0 < call_id then After (call_id - 1) else Beginning

let allocate_extra_ptrs ftype_of tpref =
  let alloc_call_extra_ptrs call =
    List.filter_map call.extra_ptrs ~f:(fun {pname;value;ptee} ->
        let addr = value in
        let ptee_type = get_pointee (get_fun_extra_ptr_type ftype_of call pname) in
        let mk_ptr value = {t=Ptr value.t;v=Addr value} in
        lprintf "allocating extra ptr in %s (%d): %s addr %Ld : %s\n"
          call.fun_name call.id pname addr (ttype_to_str ptee_type);
        match ptee with
        | Opening x ->
          add_to_known_addresses (mk_ptr (get_struct_val_value x ptee_type))
            x.break_down addr (After call.id) 0;
          None
        | Closing x ->
          add_to_known_addresses (mk_ptr (get_struct_val_value x ptee_type))
            x.break_down addr (moment_before call.id) 0;
          None
        | Changing (x,y) ->
          add_to_known_addresses (mk_ptr (get_struct_val_value x ptee_type))
            x.break_down addr (After call.id) 0;
          add_to_known_addresses (mk_ptr (get_struct_val_value y ptee_type))
            y.break_down addr (moment_before call.id) 0;
          None)
  in
  List.join (List.map (tpref.history@tpref.tip_calls) ~f:alloc_call_extra_ptrs)

let allocate_args ftype_of tpref arg_name_gen =
  let alloc_call_args (call:Trace_prefix.call_node) =
    let alloc_arg addr str_value tterm aname =
      let moment = if 0 < call.id then After (call.id - 1) else Beginning in
      lprintf "aa: looking for *%Ld (%s):\n" addr (moment_to_str moment);
      match Int64.Map.find !known_addresses addr with
      | Some spec -> known_addresses :=
          Int64.Map.set !known_addresses
            ~key:addr ~data:(List.map spec ~f:(fun spec ->
                {spec with value=update_tterm spec.value tterm}));
        lprintf "ACA found some, adding: %s\n" aname; (* TODO why are we adding directly and not through the method? *)
        None
      | None -> let p_name = arg_name_gen#generate in
        lprintf "ACA found none, inserting: %s\n" aname;
        add_to_known_addresses
          {v=Addr {v=Id p_name;t=tterm.t};t=Ptr tterm.t}
          str_value.break_down
          addr moment 0;
        Some {name=p_name;value=tterm}
    in
    let alloc_dummy_nested_ptr ptr_addr ptee_addr ptee_t =
      lprintf "adnp: looking for *%Ld\n" ptr_addr;
      match find_first_known_address
              ptr_addr
              (Ptr ptee_t)
              (moment_before call.id)
      with
      | Some _ -> None
      | None ->
        lprintf "looking for *%Ld\n" ptee_addr;
        match find_first_known_address
                ptee_addr
                ptee_t
                (moment_before call.id)
        with
        | Some a when printable_tterm a -> 
          lprintf "not allocating symbol for %Ld, because it is apparently already allocated (%s %s)\n"
                      ptee_addr (render_tterm a) (moment_to_str (moment_before call.id));
          failwith "nested ptr value dynamics too complex :/" (* TODO is this message still relevant? *)
        | _ -> let p_name = arg_name_gen#generate in
          let moment = moment_before call.id in
          lprintf "allocating nested %Ld -> %s = &%Ld:%s\n"
            ptr_addr p_name ptee_addr (ttype_to_str (Ptr ptee_t));
          add_known_symbol_at_address
            {v=Addr {v=Id p_name;t=Ptr ptee_t};t=Ptr (Ptr ptee_t)}
            ptr_addr moment 0;
          add_known_symbol_at_address
            {v=Id p_name;t=Ptr ptee_t}
            ptee_addr moment 0;
        Some {name=p_name;value={v=Undef;t=Ptr ptee_t}}
    in
    List.filter_mapi call.args ~f:(fun i {aname;value;ptr;} ->
        lprintf "filtermapi %s %s\n" call.fun_name aname;
        match ptr with
        | Nonptr -> None
        | Funptr _ -> None
        | Apathptr ->
          let addr = int64_of_sexp value in
          let t = get_fun_arg_type ftype_of call i in
          let ptee_type = get_pointee t in
          alloc_arg addr {full=None;sname=None;break_down=[]} {v=Undef;t=ptee_type;} aname
        | Curioptr ptee ->
          let addr = int64_of_sexp value in
          let t = get_fun_arg_type ftype_of call i in
          lprintf "%s fun argument %d type is %s\n" call.fun_name i (ttype_to_str t);
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
                                                   ptee.before ptee_type) aname)
  in
  List.join (List.map (tpref.history@tpref.tip_calls) ~f:alloc_call_args)

let make_lemma_args_hack (args: tterm list) =
  let replaced_args = List.map args ~f:(fun arg -> if is_pointer arg then append_id_in_tterm_id_starting_with "arg" "bis" arg else arg) in
  List.map replaced_args ~f:render_tterm

let get_lemmas_before (ftype_of,_) fun_name =
  (ftype_of fun_name).lemmas_before

let get_fun_exptr_types (_,guessed_types) call_id =
  (Int.Map.find_exn guessed_types call_id).extra_ptr_types

let compose_pre_lemmas ftype_of fun_name call_id args arg_types tmp_gen ~is_tip =
  (List.map (get_lemmas_before ftype_of fun_name) ~f:(fun l ->
       l {args=make_lemma_args_hack args;
          arg_exps=args;tmp_gen;is_tip;arg_types;
          exptr_types=get_fun_exptr_types ftype_of call_id;
          ret_type=get_fun_ret_type ftype_of call_id}))

let extract_fun_args ftype_of (call:Trace_prefix.call_node) =
  let get_allocated_arg (arg: Trace_prefix.arg) arg_type =
    let ptee_t = get_pointee arg_type in
    let addr = int64_of_sexp arg.value in
    let arg_var = find_first_symbol_by_address
        addr
        ptee_t
        (moment_before call.id)
    in
    match arg_var with
    | Some n -> n
    | None -> {v=(Utility (Ptr_placeholder addr));
               t=arg_type}
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
            begin
              let addr = get_sexp_value addr (Ptr t) in
              match addr with
              | {v=Int x;t=_} -> if (x = 0) then
                  get_allocated_arg arg a_type
                else begin
                  let key = Int64.of_int x in
                  (* First look for the address (the value the argument point to),
                     found in the pointee. *)
                  match find_first_known_address key t (moment_before call.id) with
                  | Some n -> {v=Addr n; t=Ptr t}
                  | None ->
                    (* Next try to find the address of the argument itself.
                       May be it was already allocated. *)
                    match find_first_known_address
                            (int64_of_sexp arg.value)
                            t
                            (moment_before call.id)
                    with
                    | Some n -> n
                    | None -> failwith ("nested pointer to unknown: " ^
                                        (Int.to_string x) ^ " -> " ^
                                        (Int64.to_string (int64_of_sexp arg.value)))
                end
              | _ -> get_allocated_arg arg a_type
            end
          | _ -> get_allocated_arg arg a_type)

let get_lemmas_after (ftype_of, _) fun_name =
  (ftype_of fun_name).lemmas_after

let compose_post_lemmas ~is_tip ftype_of fun_name call_id ret_spec args arg_types tmp_gen =
  let ret_spec = match ret_spec with
    | Some ret_spec -> ret_spec
    | None -> {name="";value={v=Undef;t=Unknown}}
  in
  let result = render_tterm ret_spec.value in
  List.map (get_lemmas_after ftype_of fun_name)
    ~f:(fun l -> l {ret_name=ret_spec.name;ret_val=result;
                    args=make_lemma_args_hack args;
                    arg_exps=args;tmp_gen;is_tip;arg_types;
                    exptr_types=get_fun_exptr_types ftype_of call_id;
                    ret_type=get_fun_ret_type ftype_of call_id})

let deref_tterm {v;t} =
  simplify_tterm {v = Deref {v;t};
                  t = get_pointee t}

let rec is_empty_struct_val {sname=_;full;break_down} =
  full = None && (List.for_all break_down ~f:(fun {fname=_;value;addr=_} -> is_empty_struct_val value))

let compose_args_post_conditions (call:Trace_prefix.call_node) ftype_of fun_args =
  List.filter_mapi call.args ~f:(fun i arg ->
      match arg.ptr with
      | Nonptr -> None
      | Funptr _ -> None
      | Apathptr -> None
      | Curioptr ptee ->
        if is_empty_struct_val ptee.after then None
        else match ptee.after.full with
        | Some x when (Sexp.to_string x = "0" && arg.aname = "mbuf") ->
            begin match List.nth_exn fun_args i with
            | {v=Addr fun_arg_val;t=_} ->
                Some {lhs=fun_arg_val;rhs={v=Int 0;t=Uint32}}
            | _ -> failwith "Write your own special case. Sorry." end
        | _ ->
            let key = int64_of_sexp arg.value in
            let arg_type = (get_fun_arg_type ftype_of call i) in
            lprintf "trying to process key:%Ld argtype: %s\n" key (ttype_to_str arg_type);
            match find_first_symbol_by_address
                    key arg_type (moment_before call.id)
            with
            | Some out_arg ->
              lprintf "processing %s argptr: %s| strval: %s in %s\n" 
                      arg.aname (ttype_to_str out_arg.t)
                      (render_tterm (get_struct_val_value ptee.after out_arg.t)) call.fun_name;
              begin match get_struct_val_value ptee.after (get_pointee out_arg.t) with
              | {v=Utility (Ptr_placeholder addr);t=Ptr ptee} ->
                begin
                  match find_first_known_address addr ptee (After call.id) with
                  | Some value ->
                    lprintf "found an interesting pointer value: %s\n" (render_tterm value);
                    Some {lhs=deref_tterm out_arg;
                          rhs=value}
                  | None -> None
                end
              | {v=Int _;t=_} ->
                lprintf "not processing a post cond in arg %s\n" arg.aname; None
              (* XXX: here, suck the value from the known_addresses
                 to generate a complex post condition*)
              (* Skip the two layer pointer.
                 TODO: maybe be allow special case of Zeroptr here.*)
              | value -> lprintf "CAPC %s ?= %s\n" (render_tterm (deref_tterm out_arg)) (render_tterm value);
                Some {lhs=deref_tterm out_arg;
                      rhs=value}
              end
            | None -> lprintf "not processing a post cond because 2-layer in %s\n" arg.aname; None (* The variable is not allocated,
                              because it is a 2-layer pointer.*))

let compose_extra_ptrs_post_conditions (call:Trace_prefix.call_node)
  ftype_of =
  let gen_post_condition_of_struct_val (val_before : Ir.tterm) val_now =
    lprintf "postconditions for %s: %s\n" call.fun_name (ttype_to_str val_before.t);
    match get_struct_val_value
            val_now (get_pointee val_before.t) with
    | {v=Int _;t=_} -> lprintf "CEPPC ignoring int for some reason, val_before=%s\n" (render_tterm val_before); None
    (* Skip the two layer pointer.
       TODO: maybe be allow special case of Zeroptr here.*)
    | value -> lprintf "CEPPC skipping 2-pointer: %s: %s  ?=?  %s: %s\n" (render_tterm (deref_tterm val_before)) (ttype_to_str (deref_tterm val_before).t) (render_tterm value) (ttype_to_str value.t);
      Some {lhs=deref_tterm val_before;
            rhs=value}
  in
  List.filter_map call.extra_ptrs ~f:(fun {pname;value;ptee} ->
      let key = value in
      match find_first_symbol_by_address key
              (get_fun_extra_ptr_type ftype_of call pname) (After call.id) with
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

let take_extra_ptrs_into_pre_cond ptrs call ftype_of =
  let gen_eq_by_struct_val (var_ptr : Ir.tterm) value_now =
    match get_struct_val_value value_now (get_pointee var_ptr.t) with
    | {v=Undef;t=_} -> None
    | y -> Some {lhs=deref_tterm var_ptr;rhs=y}
  in
  let moment_before = moment_before call.id in
  List.filter_map ptrs ~f:(fun {pname;value;ptee} ->
      (* TODO: this does not always work. it may miss some
         argptr symbols, e.g. because they were not
         registered in known_addresses. *)
      match find_first_symbol_by_address
              value
              (get_fun_extra_ptr_type ftype_of call pname)
              moment_before
      with
      | None -> lprintf "not found extra: %s %s. ignoring\n" call.fun_name pname;
        None
      | Some x ->
        lprintf "settled on extra %s %s => %s : %s\n" call.fun_name pname (render_tterm x) (ttype_to_str x.t);
        match ptee with
        | Opening _ -> lprintf "scratch that..."; None
        | Closing o -> gen_eq_by_struct_val x o
        | Changing (o,_) -> gen_eq_by_struct_val x o)

let allocate_dummy addr t =
  let name = ("dummy_" ^ (Int64.to_string addr)) in
  allocated_dummies := {vname=name; t={w=Noidea;
                                       s=Noidea;
                                       precise=t}}::!allocated_dummies;
  known_addresses :=
    Int64.Map.set !known_addresses
      ~key:addr ~data:[{value={v=Id name;t}; callid=Beginning;
                        str_depth=0; tt=t;
                        breakdown=String.Map.empty}];
  {v=Id name;t}

let take_arg_ptrs_into_pre_cond (args : Trace_prefix.arg list) call ftype_of =
  let moment_before = moment_before call.id in
  List.filter_mapi args ~f:(fun i arg ->
      lprintf "checking arg %s\n" arg.aname;
      match arg.ptr with
      | Nonptr -> None
      | Funptr _ -> None
      | Apathptr -> None
      | Curioptr ptee -> begin
          let addr = int64_of_sexp arg.value in
          match find_first_symbol_by_address
                  addr
                  (get_fun_arg_type ftype_of call i)
                  moment_before
          with
          | None -> lprintf "TAPIPC not found: %s %s. ignoring\n" call.fun_name arg.aname;
            None
          | Some x ->
            lprintf "TAPIPC arg. settled on %s %s => %s : %s\n" call.fun_name arg.aname (render_tterm x) (ttype_to_str x.t);
            match get_struct_val_value ptee.before (get_pointee x.t) with
            | {v=Undef;t=_} -> lprintf "TAPIPC scratch that...\n"; None
            | y -> Some {lhs={v=Deref x;t=y.t};rhs=y}
        end)

let fixup_placeholder_ptrs_in_tterm moment tterm ~need_symbol =
  let replace_placeholder = function
    | {v=Utility (Ptr_placeholder addr); t=Ptr ptee_t} ->
      lprintf "fixing placeholder for %Ld (%s)\n" addr (if need_symbol then "symbol" else "addr");
      let search_function =
        if need_symbol then
          find_first_symbol_by_address else
          find_first_known_address
      in
      begin match ptee_t, search_function addr (Ptr ptee_t) moment with
        | Unknown, _ -> failwith ("Unresolved placeholder of unknown type:" ^
                                  (render_tterm tterm))
        | _, Some x -> Some x
        | _, None -> let dummy_value = allocate_dummy addr ptee_t in
          Some {v=Addr dummy_value; t=Ptr ptee_t}
      end
    | {v=Utility _;t} ->
      failwith ("Ptr placeholder type is not a pointer:" ^
                (render_tterm tterm) ^ " : " ^ (ttype_to_str t))
    | x -> lprintf "fxphdr called on %s\n" (render_tterm x); None
  in
  lprintf "fixup_placeholder_ptrs_in_tterm called upon %s\n" (render_tterm tterm);
  call_recursively_on_tterm replace_placeholder tterm

let fixup_placeholder_ptrs moment vars =
  List.map vars ~f:(fun {name;value} ->
    {name;value=fixup_placeholder_ptrs_in_tterm moment value ~need_symbol:false})

let fixup_placeholder_ptrs_in_eq_cond moment {lhs;rhs} =
  lprintf "fixing pph in %s == %s\n" (render_tterm lhs) (render_tterm rhs);
  match rhs.v with
  | Utility (Ptr_placeholder addr) ->
    begin match find_first_known_address addr rhs.t moment with
      | Some x -> {lhs=lhs; rhs=x}
      | None ->
        known_addresses := (* TODO why are we not using the method for this? *)
          Int64.Map.set !known_addresses
            ~key:addr ~data:[{value=lhs; callid=moment;
                              str_depth=0; tt=rhs.t;
                              breakdown=String.Map.empty}];
        {lhs=lhs;rhs=lhs}
    end
  | _ ->
    {lhs=fixup_placeholder_ptrs_in_tterm moment lhs ~need_symbol:true;
     rhs=fixup_placeholder_ptrs_in_tterm moment rhs ~need_symbol:false}

let extract_common_call_context
    ftype_of call ret_spec args =
  let ret_type = get_fun_ret_type ftype_of call.id in
  let pre_lemmas = ["Render lemmas at the last moment"] in
  let application =
    (simplify_tterm {v=Apply (call.fun_name,args);
                     t=Unknown}).v
  in
  let extra_pre_conditions =
    (take_extra_ptrs_into_pre_cond call.extra_ptrs call ftype_of) @ (take_arg_ptrs_into_pre_cond call.args call ftype_of) in
  let post_lemmas = ["Render lemmas at the last moment"] in
  let ret_name = match ret_spec with
    | Some ret_spec -> Some ret_spec.name
    | None -> None
  in
  (* TODO fixup placeholders in args here *)
  let extra_pre_conditions = List.map extra_pre_conditions
       ~f:(fixup_placeholder_ptrs_in_eq_cond (After call.id))
  in
  let application = (fixup_placeholder_ptrs_in_tterm
                    (After call.id)
                    {v=application;t=Unknown}
                    ~need_symbol:true).v
  in
  {extra_pre_conditions;pre_lemmas;
   application;
   post_lemmas;ret_name;ret_type;call_id=call.id}

let convert_ctxt_list l = List.map l ~f:(fun e ->
    (get_sexp_value e Boolean))

let extract_hist_call ftype_of call rets =
  lprintf "extract hist call: %s\n" call.fun_name;
  let args = extract_fun_args ftype_of call in
  let args_post_conditions = compose_args_post_conditions call ftype_of args in
  let args_post_conditions =
    (compose_extra_ptrs_post_conditions call ftype_of)@args_post_conditions
  in
  let args_post_conditions =
    List.map args_post_conditions ~f:(fixup_placeholder_ptrs_in_eq_cond (After call.id))
  in
  let post_statements = convert_ctxt_list call.ret_context in
  let post_statements = List.map post_statements ~f:(fixup_placeholder_ptrs_in_tterm
                                                     (After call.id)
                                                     ~need_symbol:false) in  
  match Int.Map.find rets call.id with
  | Some ret ->
    {context=extract_common_call_context
         ftype_of call (Some ret) args;
     result={args_post_conditions;ret_val=ret.value;post_statements}}
  | None ->
    {context=extract_common_call_context
         ftype_of call None args;
     result={args_post_conditions;ret_val={t=Unknown;v=Undef;};post_statements}}

let extract_tip_calls ftype_of calls rets =
  lprintf "extract tip call: %s\n" (List.hd_exn calls).fun_name;
  let call = List.hd_exn calls in
  let args = extract_fun_args ftype_of call in
  let context = extract_common_call_context
      ftype_of call (Int.Map.find rets call.id) args
  in
  let get_ret_val call =
    match Int.Map.find rets call.id with
    | Some ret -> ret.value
    | None -> {t=Unknown;v=Undef;}
  in
  let results =
    match calls with
    | [] -> failwith "There must be at least one tip call."
    | _ ->
      List.map calls ~f:(fun tip ->
          let args_post_conditions = compose_args_post_conditions tip ftype_of args in
          let ret_val = get_ret_val tip in
          let post_statements = convert_ctxt_list tip.ret_context in
          let args_post_conditions = List.map args_post_conditions
                                              ~f:(fixup_placeholder_ptrs_in_eq_cond
                                                  (After context.call_id)) in
          let ret_val = fixup_placeholder_ptrs_in_tterm (After context.call_id) ret_val ~need_symbol:false in
          let post_statements = List.map post_statements
                                         ~f:(fixup_placeholder_ptrs_in_tterm
                                             (After context.call_id)
                                             ~need_symbol:false) in
          {args_post_conditions;ret_val;post_statements})
  in
  lprintf "got %d results for tip-call\n" (List.length results);
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
   | [] -> failwith "There must be at least one tip call."
   | hd :: tail -> let call_context = convert_ctxt_list hd.call_context in
     assert (List.for_all tail ~f:(fun tip ->
         call_context = convert_ctxt_list tip.call_context));
     call_context)

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

let typed_vars_to_varspec free_vars =
  List.fold (String.Map.data free_vars) ~init:String.Map.empty
    ~f:(fun acc {vname;t;} ->
        String.Map.add_exn acc ~key:vname
          ~data:{name=vname;value={v=Undef;t=ttype_of_guess t}})

let guess_dynamic_types (basic_ftype_of : string -> fun_spec) pref =
  let type_match tag t str_val =
    (match str_val.sname with
       Some sname when String.equal sname tag -> true | _ -> false)
    ||
    (match t with
     | Ptr (Str (struct_name, fields)) ->
       begin match str_val.sname with
         | Some sname ->
           if String.equal sname struct_name then begin
             assert (List.for_all str_val.break_down
                       ~f:(fun {fname;value=_;addr=_} ->
                           List.exists fields ~f:(fun (name,_) ->
                               String.equal name fname)));
             true
           end else false
         | None ->
           List.for_all str_val.break_down
             ~f:(fun {fname;value=_;addr=_} ->
                 List.exists fields ~f:(fun (name,_) -> String.equal name fname)
                 (* One level introspection should be enough *))
       end
     | _ -> false)
  in
  let find_type_match ts str_val val_name call =
    match List.find ts ~f:(fun (tag,t) -> type_match tag t str_val) with
    | Some (_,tt) -> lprintf "guessed %s for %s/%d#%s\n" (ttype_to_str tt)
                             call.fun_name call.id val_name;
                     tt
    | None -> failwith
                ("Can not guess a dynamic type for " ^
                 call.fun_name ^ "/" ^ Int.to_string call.id ^
                 " " ^ val_name)
  in
  let guess_type ts str_val val_name call =
    match ts with
    | Static t -> t
    | Dynamic ts -> find_type_match ts str_val val_name call
  in
  List.fold (pref.history @ pref.tip_calls)
    ~init:(Int.Map.empty:guessed_types Int.Map.t) ~f:(fun acc call ->
        let arg_decl_types = (basic_ftype_of call.fun_name).arg_types in
        let arg_type_guesses =
          List.foldi (List.zip_exn call.args arg_decl_types)
            ~init:[]
            ~f:(fun (n:int) (acc:ttype list) ((arg:Trace_prefix.arg),
                                              (ts:type_set)) ->
                 match ts, arg with
                 | Dynamic ts, {aname=_; value=_; ptr=Curioptr ptee} ->
                   (find_type_match ts ptee.before
                      ("argument # " ^ Int.to_string n)
                      call)::acc
                 | Static t, _ -> t::acc
                 | Dynamic _, _ -> failwith ("Only a structure types can \
                                              be guessed. Arg " ^ arg.aname ^
                                             " of " ^ call.fun_name ^
                                             " is not a structure."))
        in
        let ex_ptr_type_guesses =
          let ex_ptr_decl_types =
            String.Map.of_alist_exn (basic_ftype_of call.fun_name).extra_ptr_types
          in
          let all_ptrs = function Static t -> Static (Ptr t)
                                | Dynamic ts ->
                                  Dynamic (List.map ts ~f:(fun (tag,t) ->
                                      (tag, Ptr t)))
          in
          List.fold call.extra_ptrs
            ~init:String.Map.empty
            ~f:(fun acc {pname;value=_;ptee} ->
                let ts =
                  match String.Map.find ex_ptr_decl_types pname with
                  | Some x -> x
                  | None -> failwith ("Can not find extraptr declaration for " ^
                                     pname ^ " in function " ^ call.fun_name)
                in
                match ptee with
                | Opening x
                | Closing x
                | Changing (x,_) ->
                  String.Map.add_exn acc ~key:pname
                    ~data:(get_pointee
                             (guess_type
                                (all_ptrs ts) x ("ex_ptr: " ^ pname) call)))
        in
        let ret_type_guess =
          let ret_type_spec = (basic_ftype_of call.fun_name).ret_type in
          match call.ret, ret_type_spec with
          | Some {value=_;ptr=Curioptr ptee}, _ ->
            guess_type ret_type_spec ptee.before "ret_val" call
          | Some {value=_;ptr=_}, Dynamic _ ->
            failwith ("Can not guess nonstructural type for\
                       return value of " ^ call.fun_name)
          | _, Static t -> t
          | None,_ -> Void
        in
        Int.Map.add_exn acc ~key:call.id
          ~data:{ret_type=ret_type_guess;
                 arg_types=List.rev arg_type_guesses;
                 extra_ptr_types=ex_ptr_type_guesses})

let call_fun_name call_context =
  match call_context.application with
  | Apply (fun_name,_) -> fun_name
  | x -> failwith ((render_term x) ^ " is not a function application")

let call_args call_context =
  match call_context.application with
  | Apply (_,args) -> args
  | x -> failwith ((render_term x) ^ " is not a function application")

let ttypes_of_tterms (tterms : tterm list) =
  List.map tterms ~f:(fun t -> t.t)

let render_hist_lemmas ftype_of hist_calls =
  List.map hist_calls ~f:(fun (call : hist_call) ->
      let ret_spec = match call.context.ret_name with
        | Some name -> Some {name;value=call.result.ret_val}
        | None -> None
      in
      let tmp_gen =
        gen_unique_tmp_name (string_of_int call.context.call_id)
      in
      {call with
       context = {call.context with
                  pre_lemmas = compose_pre_lemmas
                      ftype_of
                      (call_fun_name call.context)
                      call.context.call_id
                      (call_args call.context)
                      (ttypes_of_tterms (call_args call.context))
                      tmp_gen
                      ~is_tip:false;
                  post_lemmas = compose_post_lemmas
                      ~is_tip:false
                      ftype_of
                      (call_fun_name call.context)
                      call.context.call_id
                      ret_spec
                      (call_args call.context)
                      (ttypes_of_tterms (call_args call.context))
                      tmp_gen}})

let render_tip_lemmas ftype_of (tip_call : tip_call) =
  let ret_spec = match tip_call.context.ret_name with
    | Some name -> Some {name;value=(List.hd_exn tip_call.results).ret_val}
    | None -> None
  in
  let tmp_gen = gen_unique_tmp_name "tip" in
  {tip_call with
   context = {tip_call.context with
              pre_lemmas = compose_pre_lemmas
                  ftype_of
                  (call_fun_name tip_call.context)
                  tip_call.context.call_id
                  (call_args tip_call.context)
                  (ttypes_of_tterms (call_args tip_call.context))
                  tmp_gen
                  ~is_tip:false;
              post_lemmas = compose_post_lemmas
                  ~is_tip:false
                  ftype_of
                  (call_fun_name tip_call.context)
                  tip_call.context.call_id
                  ret_spec
                  (call_args tip_call.context)
                  (ttypes_of_tterms (call_args tip_call.context))
                  tmp_gen}}

let fix_term (known_vars: var_spec list) term =
  fix_type_of_id_in_tterm known_vars term

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
  (* Int.Map.iteri guessed_dyn_types ~f:(fun ~key ~data ->
   *     lprintf "%d -> ret:%s \n" key (ttype_to_str data.ret_type);
   *     List.iter data.arg_types ~f:(fun t ->
   *         lprintf "arg type: %s\n" (ttype_to_str t))); *)
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
  (* let double_ptr_args = get_double_ptr_args ftype_of pref in *)
  let arguments = (allocate_extra_ptrs ftype_of pref) in (* ORDER IS IMPORTANT HERE, EXTRA PTRS FIRST otherwise args that contain them fail... *)
  let arguments = (allocate_args ftype_of pref (name_gen "arg"))@arguments in
  let rets = allocate_rets ftype_of pref in
  (* let (rets, tip_dummies) = allocate_tip_ret_dummies ftype_of pref.tip_calls rets in *)
  let (hist_calls,tip_call) = extract_calls_info ftype_of pref rets in
  let arguments = fixup_placeholder_ptrs Beginning arguments in
  let hist_calls = render_hist_lemmas ftype_of hist_calls in
  let tip_call = render_tip_lemmas ftype_of tip_call in
  let context_assumptions = collect_context pref in
  let cmplxs = !allocated_complex_vals in

  (* And now for some type-assignments... *)
  let known_vars = (arguments@(String.Map.data free_vars)@(String.Map.data cmplxs)) in
  let fix_condition cond = {lhs=fix_term known_vars cond.lhs;rhs=fix_term known_vars cond.rhs} in
  let context_assumptions = List.map context_assumptions ~f:(fix_term known_vars) in
  let hist_calls = List.map hist_calls ~f:(fun c -> {context={c.context with extra_pre_conditions=(List.map c.context.extra_pre_conditions ~f:fix_condition)};
                                                     result={c.result with args_post_conditions=(List.map c.result.args_post_conditions ~f:fix_condition)}}) in
  let tip_call = {context={tip_call.context with extra_pre_conditions=(List.map tip_call.context.extra_pre_conditions ~f:fix_condition)};
                  results=List.map tip_call.results ~f:(fun r -> {r with args_post_conditions=(List.map r.args_post_conditions ~f:fix_condition);
                                                                         post_statements=List.map r.post_statements ~f:(fix_term known_vars)})} in

  (* Do not render the allocated_dummies *)
  {preamble;free_vars;arguments;
   cmplxs;context_assumptions;hist_calls;tip_call;
   export_point;finishing;
   complete_event_loop_iteration = inside_iteration && finishing_iteration;
   semantic_checks=""}
