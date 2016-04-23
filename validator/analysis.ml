open Core.Std
open Ir

let log str =
  if true then ()
  else print_string str

let lprintf fmt = ksprintf log fmt

let extract_equalities ass_list =
  List.partition_tf ass_list ~f:(function {v=Bop(Eq,_,_);t=_} -> true | _ -> false)

let remove_trivial_eqs eqs =
  List.filter eqs ~f:(function {v=Bop(Eq,lhs,rhs);t=_} -> not (term_eq lhs.v rhs.v) | _ -> true)

(* The equalities that do not reduce to a simple variable renaming:
   anything except (a = b).*)
let get_meaningful_equalities eqs =
  List.filter eqs ~f:(function
      | {v=Bop (Eq,lhs,rhs);t=_} ->
        begin
          match lhs.v,rhs.v with
          | Id _, Id _ -> false
          | _, _ -> true
        end
      | _ -> failwith "only equalities here")

let synonimize_term_in_tterms a b tterms =
  List.fold tterms ~init:tterms ~f:(fun acc tterm ->
      let acc =
        if tterm_contains_term tterm a then
          (replace_term_in_tterm a b tterm)::acc
        else acc
      in
      if tterm_contains_term tterm b then
        (replace_term_in_tterm b a tterm)::acc
      else acc)

let synonimize_by_equalities ass_list eqs =
  List.fold eqs ~init:ass_list
    ~f:(fun acc eq ->
         match eq.v with
         | Bop(Eq,lhs,rhs) ->
           synonimize_term_in_tterms lhs.v rhs.v acc
         | _ -> failwith "eqs must contain only equalities")

let get_ids_from_tterm tterm =
  let rec impl = function
    | Bop (_,lhs,rhs) ->
      (impl lhs.v)@(impl rhs.v)
    | Apply (_,args) ->
      List.join (List.map args ~f:(fun arg -> impl arg.v))
    | Id x -> [x]
    | Struct (_,fds) ->
      List.join (List.map fds ~f:(fun fd -> impl fd.value.v))
    | Int _ -> []
    | Bool _ -> []
    | Not tterm -> impl tterm.v
    | Str_idx (tterm,_) -> impl tterm.v
    | Deref tterm -> impl tterm.v
    | Fptr _ -> []
    | Addr tterm -> impl tterm.v
    | Cast (_,tterm) -> impl tterm.v
    | Undef -> []
  in
  List.dedup (impl tterm.v)

let index_assumptions (ass_list:tterm list) =
  List.fold ass_list ~init:String.Map.empty ~f:(fun acc ass ->
      let ids = get_ids_from_tterm ass in
      let ass_with_ids = (ass,ids) in
      List.fold ids ~init:acc ~f:(fun acc id ->
          String.Map.add acc ~key:id
            ~data:(match String.Map.find acc id with
                | Some ass_list -> ass_with_ids::ass_list
                | None -> [ass_with_ids])))

let take_relevant (ass_list:tterm list) interesting_ids =
  let map = index_assumptions ass_list in
  let interesting_ids = String.Set.of_list interesting_ids in
  let rec take_relevant_impl interesting_ids processed =
    let relevant_asses =
      List.join (List.map (String.Set.to_list interesting_ids) ~f:(fun id ->
        match String.Map.find map id with
        | Some asses_list -> asses_list
        | None -> []))
    in
    let new_ids = String.Set.diff
        (String.Set.of_list (List.join (List.map relevant_asses ~f:(fun (_,ids) -> ids))))
        processed
    in
    let relevant_asses = (List.map relevant_asses ~f:(fun (ass,_) -> ass)) in
    if (String.Set.is_empty new_ids) then (relevant_asses,processed)
    else
      let (relevant_sttmts,relevant_ids) =
        take_relevant_impl new_ids (String.Set.union interesting_ids processed)
      in
      (relevant_sttmts@relevant_asses,relevant_ids)
  in
  let (relevant_sttmts,relevant_ids) =
    take_relevant_impl interesting_ids String.Set.empty
  in
  (List.dedup relevant_sttmts,String.Set.to_list relevant_ids)

let tterm_weight tterm = String.length (render_tterm tterm)

let reduce_by_eqs (sttmts: tterm list) (eqs: tterm list) keep =
  List.fold eqs ~init:sttmts
    ~f:(fun acc eq ->
         match eq.v with
         | Bop(Eq,lhs,rhs) ->
           let (light,heavy) =
             if (tterm_weight lhs) > (tterm_weight rhs) ||
                is_constt rhs ||
                List.exists keep ~f:(tterm_contains_term rhs)
             then
               (rhs,lhs)
             else
               (lhs,rhs)
           in
           if (tterm_weight light) - (tterm_weight heavy) < 10 then
             replace_term_in_tterms heavy.v light.v acc
           else
             acc
         | _ -> failwith "eqs must contain only equalities")

let rec expand_struct_eq sttmt : tterm list =
  match sttmt.v with
  | Bop(Eq,{v=Struct(_,fds);t=_},rhs) ->
    List.join
      (List.map fds ~f:(fun fd ->
           expand_struct_eq
             ({v=Bop(Eq,fd.value,{v=Str_idx(rhs,fd.name);t=fd.value.t});t=sttmt.t})))
  | Bop(Eq,lhs,{v=Struct(name,fds);t=rt}) ->
    expand_struct_eq {v=Bop(Eq,{v=Struct(name,fds);t=rt},lhs);t=sttmt.t}
  | _ -> [sttmt]

let expand_struct_eqs sttmts =
  List.join (List.map sttmts ~f:expand_struct_eq)

let reduce_struct_idxes_in_tterm sttmt =
  sttmt |> call_recursively_on_tterm (function
      | Str_idx ({v=Struct(_,fields);t=_}, field) ->
        Some (List.find_exn fields ~f:(fun {name;value} ->
          name = field)).value.v
      | _ -> None
    )

let reduce_struct_idxes sttmts =
  List.map sttmts ~f:reduce_struct_idxes_in_tterm

let simplify ass_list keep =
  let remove_double_negation a =
    a |> call_recursively_on_tterm (fun term ->
        match term with
        | Not {v=Not tt;t=_} -> Some tt.v
        | _ -> None)
  in
  let remove_true_eq al =
    List.map al ~f:(function {v=Bop(Eq,{v=Bool true;t=_},x);t=_} -> x
                           | x -> x) in
  let remove_trues al =
    List.filter al ~f:(function {v=Bool true;t=_} -> false | _ -> true)
  in
  let ass_list = remove_true_eq ass_list in
  let ass_list = List.map ass_list ~f:remove_double_negation in
  let ass_list = reduce_struct_idxes ass_list in
  let (eqs,non_eq_assumptions) = (extract_equalities ass_list) in
  let eqs = remove_trivial_eqs eqs in
  let ass_list = non_eq_assumptions in
  let eqs = expand_struct_eqs eqs in
  let eqs = reduce_struct_idxes eqs in
  let ass_list = (*synonimize_by_equalities ass_list eqs*)
    reduce_by_eqs ass_list eqs keep in
  let eqs = reduce_by_eqs eqs eqs keep in
  let ass_list = (get_meaningful_equalities eqs) @ ass_list in
  remove_trues ass_list

let not_stronger op1 op2 =
  if op1=op2 then true else
    match op1,op2 with
    | Le,Lt -> true
    | Ge,Gt -> true
    | _,_ -> false

type assignment = (string*term)

let canonicalize statements =
  let canonicalize1 sttmt =
    match sttmt with
    | {v=Bop (Eq,{v=Bool false;_},rhs);t} ->
      {v=Not rhs;t}
    | {v=Bop (Ge,lhs,rhs);t} -> {v=Bop(Le,rhs,lhs);t}
    | {v=Bop (Gt,lhs,rhs);t} -> {v=Bop(Lt,rhs,lhs);t}
    | _ -> sttmt
  in
  List.map statements ~f:canonicalize1

let prepare_assertions tip_res tip_ret_name tip_ret_type =
  let exists_such =
    (List.map tip_res.args_post_conditions
       ~f:(fun spec -> {v=Bop (Eq,{v=Id spec.name;t=Unknown},
                               spec.value);
                        t=Boolean})) @
    tip_res.post_statements
  in
  match tip_ret_name with
  | Some ret_name ->
    {v=Bop (Eq,{v=Id ret_name;t=tip_ret_type},
            tip_res.ret_val);t=Boolean} :: exists_such
  | None -> exists_such

let apply_assignments assignments ir =
  {ir with
   free_vars = List.fold assignments ~init:ir.free_vars
       ~f:(fun acc (name,value) ->
           let prev = String.Map.find_exn acc name in
           String.Map.add acc ~key:name
             ~data:{name;value={t=prev.value.t;v=value}})}

let apply_assignments_to_statements assignments statements =
  List.fold assignments ~init:statements
    ~f:(fun acc (name,value) ->
        replace_term_in_tterms (Id name) value acc)

let find_assignment assumptions assertions var =
  lprintf "searching for %s:{\n given:\n" var;
  List.iter assumptions ~f:(fun x -> lprintf "%s\n" (render_tterm x));
  lprintf "such that:\n";
  List.iter assertions ~f:(fun x -> lprintf "%s\n" (render_tterm x));
  lprintf "}\n";
  List.find_map assertions ~f:(fun assertion ->
      match assertion with
      | {v=Bop (Eq, {v=Id lhs;_}, rhs);_}
        when lhs = var ->
        Some (var,rhs.v)
      | {v=Bop (Eq, lhs, {v=Id rhs;_});_}
        when rhs = var ->
        Some (var,lhs.v)
      | {v=Bop (Le, {v=Int lhs;_}, {v=Id rhs;_});_}
        when rhs = var -> (* TODO: preoritize this assignments
                             less than the above ones*)
        lprintf "exploiting inequality: %d <= %s\n" lhs rhs;
        Some (var,Int lhs)
      | _ -> None)

let find_assignments assumptions assertions vars =
  List.join (List.map vars ~f:(fun var ->
      let (assertions,rel_ids) = take_relevant assertions [var] in
      let (assumptions,_) = take_relevant assumptions rel_ids in
      match find_assignment assumptions assertions var with
      | Some assignment -> [assignment]
      | None -> []))

let expand_conjunctions sttmts =
  let rec expand_sttmt = function
    | {v=Bop (And,lhs,rhs);_} -> (expand_sttmt lhs)@(expand_sttmt rhs)
    | x -> [x]
  in
  List.join (List.map sttmts ~f:expand_sttmt)

let expand_fixpoints_in_tterm tterm =
  let rec impl tterm =
    match tterm with
    | Apply (fname,args) ->
      begin
        match String.Map.find Function_spec.fixpoints fname with
        | Some body ->
          Some (List.foldi args ~init:body
                  ~f:(fun i acc arg ->
                      replace_term_in_tterm (Id (sprintf "Arg%d" i))
                        arg.v acc)).v
        | None -> None
      end
    | _ -> None
  in
  call_recursively_on_tterm impl tterm

let expand_fixpoints sttmts =
  List.map sttmts ~f:expand_fixpoints_in_tterm

let is_assignment_justified var value executions =
  lprintf "justifying assignment %s = %s\n" var (render_term value);
  let valid = List.for_all executions ~f:(fun assumptions ->
      let (assumptions,_) = take_relevant assumptions [var] in
      let assumptions = expand_fixpoints assumptions in
      let assumptions = simplify assumptions [Id var] in
      let assumptions = canonicalize assumptions in
      let mod_assumptions = replace_term_in_tterms (Id var) value assumptions in
      lprintf "comparing:\n";
      List.iter assumptions ~f:(fun ass -> lprintf "%s\n" (render_tterm ass));
      lprintf "with\n";
      List.iter mod_assumptions ~f:(fun ass -> lprintf "%s\n" (render_tterm ass));
      List.for_all mod_assumptions ~f:(fun mod_assumption ->
          List.exists assumptions
            ~f:(fun assumption ->
                term_eq assumption.v mod_assumption.v)))
  in
  lprintf "%s\n" (if valid then "justified" else "unjustified");
  valid

let induce_symbolic_assignments ir executions =
  let fr_var_names = List.map (String.Map.data ir.free_vars) ~f:(fun spec -> spec.name) in
  lprintf "free vars: \n";
  List.iter fr_var_names ~f:(fun vn -> lprintf "%s\n" vn);
  let assignments = List.fold ir.tip_call.results ~init:[] ~f:(fun acc res ->
      let assertions = prepare_assertions res
          ir.tip_call.context.ret_name
          ir.tip_call.context.ret_type
      in
      let assertions = expand_conjunctions assertions in
      let assertions = expand_struct_eqs assertions in
      let assertions = apply_assignments_to_statements acc assertions in
      let assertions = canonicalize assertions in
      List.fold executions ~init:acc ~f:(fun acc assumptions ->
          let vars = String.Set.to_list
              (String.Set.diff (String.Set.of_list fr_var_names)
                 (String.Set.of_list (List.map acc ~f:fst)))
          in
          let var_ids = List.map vars ~f:(fun name -> Id name) in
          let assumptions = expand_fixpoints assumptions in
          let assumptions = apply_assignments_to_statements acc assumptions in
          let assumptions = simplify assumptions var_ids in
          let assumptions = canonicalize assumptions in
          (find_assignments assumptions assertions vars)@acc))
  in
  let justified_assignments = List.filter assignments ~f:(fun (var,value) ->
      is_assignment_justified var value executions)
  in
  apply_assignments justified_assignments ir;
