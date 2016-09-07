open Core.Std
open Ir

let no_log = true

let log str =
  if no_log then ()
  (* else print_string str *)
  else Out_channel.with_file ~append:true "analysis.log" ~f:(fun f ->
      Out_channel.output_string f str)

let start_log () =
  if no_log then ()
  else Out_channel.with_file "analysis.log" ~f:(fun _ -> ())

let lprintf fmt = ksprintf log fmt

let lprint_list lst =
  List.iter lst ~f:(fun vn -> lprintf "%s\n" vn)

let canonicalize_in_place statements =
  let rec canonicalize1 sttmt =
    match sttmt with
    | {v=Bop (Eq,{v=Bool false;_},rhs);t} ->
      {v=Not rhs;t}
    | {v=Bop (Eq,lhs,{v=Bool false;_});t} ->
      {v=Not lhs;t}
    | {v=Bop (Eq,{v=Bool true;_},rhs);t=_} ->
      canonicalize1 rhs
    | {v=Bop (Eq,lhs,{v=Bool true;_});t=_} ->
      canonicalize1 lhs
    | {v=Bop (Ge,lhs,rhs);t} -> {v=Bop(Le,rhs,lhs);t}
    | {v=Bop (Gt,lhs,rhs);t} -> {v=Bop(Lt,rhs,lhs);t}
    | _ -> sttmt
  in
  List.map statements ~f:canonicalize1

let expand_conjunctions sttmts =
  let rec expand_sttmt = function
    | {v=Bop (And,lhs,rhs);_} -> (expand_sttmt lhs)@(expand_sttmt rhs)
    | x -> [x]
  in
  List.join (List.map sttmts ~f:expand_sttmt)

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

let expand_fixpoints_in_tterm
    (fixpoints : Ir.tterm Core.Std.String.Map.t) tterm =
  let impl tterm =
    match tterm with
    | Apply (fname,args) ->
      begin
        match String.Map.find fixpoints fname with
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

let remove_double_negation sttmt =
  sttmt |> call_recursively_on_tterm (fun term ->
      match term with
      | Not {v=Not tt;t=_} -> Some tt.v
      | _ -> None)

let remove_trues sttmts =
  List.filter sttmts ~f:(function {v=Bool true;t=_} -> false | _ -> true)

let expand_fixpoints fixpoints sttmts =
  List.map sttmts ~f:(expand_fixpoints_in_tterm fixpoints)

let reduce_struct_idxes sttmt =
  sttmt |> call_recursively_on_tterm (function
      | Str_idx ({v=Struct(_,fields);t=_}, field) ->
        Some (List.find_exn fields ~f:(fun {name;value=_} ->
          name = field)).value.v
      | _ -> None
    )

(* Transform statement list to a canonical form,
   breaking down conjunctions, inlining function definitions,
   and breaking structures into separate fields. *)
let canonicalize fixpoints sttmts =
  sttmts |>
  remove_trues |>
  canonicalize_in_place |>
  expand_fixpoints fixpoints |> (*May introduce conjunctions and negations.*)
  List.map ~f:remove_double_negation |>
  expand_conjunctions |>
  expand_struct_eqs |>
  List.map ~f:reduce_struct_idxes |>
  List.dedup

let remove_trivial_eqs eqs =
  List.filter eqs ~f:(function
        {v=Bop(Eq,lhs,rhs);t=_} -> not (term_eq lhs.v rhs.v)
      | _ -> true)

let tterm_weight tterm = String.length (render_tterm tterm)

let get_replacement_pair a b keep =
  match (List.exists keep ~f:(tterm_contains_term a)),
        (List.exists keep ~f:(tterm_contains_term b)) with
  | true, true -> None
  | true, false ->
    if (tterm_weight a) > (tterm_weight b) + 50 then
      None
    else Some (b,a)
  | false, true ->
    if (tterm_weight b) > (tterm_weight a) + 50 then
      None
    else Some (a,b)
  | false, false ->
    if (tterm_weight a) > (tterm_weight b) then
      Some (a,b)
    else
      Some (b,a)

(* The equalities that are not a simple variable renaming:
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

let reduce_by_equalities vars sttmts =
  List.fold_right sttmts ~f:(fun sttmt (sttmts,eqs) ->
      let sttmt = List.fold eqs ~init:sttmt ~f:(fun acc (rfrom,rto) ->
        replace_term_in_tterm rfrom rto acc) in
      match sttmt with
      | {v=Bop (Eq,lhs,rhs);t=_} ->
        begin
          match get_replacement_pair lhs rhs vars with
          | Some (replace_from, replace_to) ->
            (sttmt::(replace_term_in_tterms replace_from.v replace_to.v sttmts),
            (replace_from.v,replace_to.v)::eqs)
          | None -> (sttmt::sttmts,eqs)
        end
      | _ -> (sttmt::sttmts,eqs)) ~init:([],[])
  |> fst
  |> remove_trivial_eqs

let simplify fixpoints vars sttmts =
  lprintf "\n\nover vars: \n";
  lprint_list (List.map vars ~f:render_term);
  let one = canonicalize fixpoints sttmts in
  lprintf "\ncanonicalized: \n";
  lprint_list (List.map one ~f:render_tterm);
  let two = reduce_by_equalities vars one in
  lprintf "\nreduced:\n";
  lprint_list (List.map two ~f:render_tterm);
  let three = canonicalize fixpoints two in
  lprintf "\ncanonicalized2: \n";
  lprint_list (List.map three ~f:render_tterm);
  let four = reduce_by_equalities vars three in
  lprintf "\nreduced2: \n";
  lprint_list (List.map four ~f:render_tterm);
  let five = reduce_by_equalities vars four in
  lprintf "\nreduced3: \n";
  lprint_list (List.map five ~f:render_tterm);
  let six = reduce_by_equalities vars five in
  lprintf "\nreduced4: \n";
  lprint_list (List.map six ~f:render_tterm);
  six

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

(*---- here ----*)

(* let synonimize_term_in_tterms a b tterms =
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
*)

let not_stronger op1 op2 =
  if op1=op2 then true else
    match op1,op2 with
    | Le,Lt -> true
    | Ge,Gt -> true
    | _,_ -> false

let prepare_assertions tip_res tip_ret_name tip_ret_type =
  let exists_such =
    (List.map tip_res.args_post_conditions
       ~f:(fun spec -> {v=Bop (Eq,spec.lhs,
                               spec.rhs);
                        t=Boolean})) @
    tip_res.post_statements
  in
  match tip_ret_name with
  | Some ret_name ->
    {v=Bop (Eq,{v=Id ret_name;t=tip_ret_type},
            tip_res.ret_val);t=Boolean} :: exists_such
  | None -> exists_such

let prepare_output_vars tip_res tip_ret_name =
  let arg_symbols =
    List.fold tip_res.args_post_conditions ~init:String.Set.empty
      ~f:(fun vars spec ->
          String.Set.union vars (String.Set.of_list (get_ids_from_tterm spec.lhs)))
  in
  match tip_ret_name with
  | Some ret_name -> Set.add arg_symbols ret_name
  | None -> arg_symbols

let prepare_output_params tip_res =
  let arg_symbols =
    List.fold tip_res.args_post_conditions ~init:String.Set.empty
      ~f:(fun vars spec ->
          String.Set.union vars (String.Set.of_list (get_ids_from_tterm spec.rhs)))
  in
  String.Set.union (String.Set.of_list (get_ids_from_tterm tip_res.ret_val)) arg_symbols

let apply_assignments assignments ir =
  {ir with
   free_vars = List.fold assignments ~init:ir.free_vars
       ~f:(fun acc (name,value) ->
           match String.Map.find acc name with
           | Some prev ->
             String.Map.add acc ~key:name
               ~data:{name;value={t=prev.value.t;v=value}}
           | None ->
             String.Map.add acc ~key:name
         ~data:{name;value={t=Unknown;v=value}})}

let apply_assignments_to_statements assignments statements =
  List.fold assignments ~init:statements
    ~f:(fun acc (name,value) ->
        replace_term_in_tterms (Id name) value acc)

let find_assignment assumptions assertions var =
  lprintf "searching for %s:{\n given:\n" var;
  List.iter assumptions ~f:(fun x -> lprintf "%s\n" (render_tterm x));
  lprintf "such that:\n";
  List.iter assertions ~f:(fun x -> lprintf "%s\n" (render_tterm x));
  let assignment =
    List.find_map assertions ~f:(fun assertion ->
        match assertion with
        | {v=Bop (Eq, {v=Id lhs;_}, rhs);_}
          when lhs = var ->
          Some (var,rhs.v)
        | {v=Bop (Eq, lhs, {v=Id rhs;_});_}
          when rhs = var ->
          Some (var,lhs.v)
        | {v=Bop (Le, {v=Int lhs;_}, {v=Id rhs;_});_}
          when rhs = var -> (* TODO: prioritize this assignments
                               less than the above ones*)
          lprintf "exploiting inequality: %d <= %s\n" lhs rhs;
          Some (var,Int lhs)
        | _ -> None)
  in
  begin
    lprintf "} ";
    match assignment with
    | Some (_,value) -> lprintf "found: %s = %s\n" var (render_term value)
    | None -> lprintf "NOTHING found\n"
  end;
  assignment

let guess_assignments assumptions assertions vars =
  List.join (List.map vars ~f:(fun var ->
      let (assertions,rel_ids) = take_relevant assertions [var] in
      let (assumptions,_) = take_relevant assumptions rel_ids in
      match find_assignment assumptions assertions var with
      | Some assignment -> [assignment]
      | None -> []))

(* let is_assignment_justified fixpoints var value executions = *)
(*   lprintf "justifying assignment %s = %s\n" var (render_term value); *)
(*   let valid = List.for_all executions ~f:(fun assumptions -> *)
(*       let orig_assumptions = assumptions |> simplify fixpoints [Id var; value] in *)
(*       let rel_assumptions = take_relevant orig_assumptions [var] |> fst |> *)
(*                             simplify fixpoints [Id var] *)
(*       in *)
(*       let mod_assumptions = *)
(*         replace_term_in_tterms (Id var) value orig_assumptions in *)
(*       lprintf "comparing:\n"; *)
(*       List.iter rel_assumptions ~f:(fun ass -> lprintf "%s\n" (render_tterm ass)); *)
(*       lprintf "with\n"; *)
(*       List.iter orig_assumptions ~f:(fun ass -> lprintf "%s\n" (render_tterm ass)); *)
(*       List.for_all mod_assumptions ~f:(fun mod_assumption -> *)
(*           match mod_assumption, value with *)
(*           | {t=Boolean;v=Bop (Eq, _, _);}, Addr _-> *)
(*             lprintf "skipping the ptr-arith %s\n" (render_tterm mod_assumption); *)
(*             (\* Numerical relations are not important for pointers *\) *)
(*             (\* TODO: the fixpoint related statements are currently stripped of *)
(*                the "= true" or "= false", which makes them somatimes *)
(*                indistinguissable from predicates. We need to keep that *)
(*                information, to make sure we respect predicates and skip the *)
(*                fixpoints operating on pointers. We need also to make sure, that *)
(*                thes skipped fixpoints do not also check for some other *)
(*                non-pointer numerical property. *\) *)
(*             true *)
(*           | _ -> *)
(*             List.exists orig_assumptions *)
(*               ~f:(fun assumption -> *)
(*                   term_eq assumption.v mod_assumption.v))) *)
(*   in *)
(*   lprintf "%s\n" (if valid then "justified" else "unjustified"); *)
(*   valid *)

let replace__addr_with_prefixed_var sttmt =
  call_recursively_on_tterm
    (function
      | Addr {v=Id x;t=_} -> Some (Id (x ^ "_addr"))
      | _ -> None) sttmt

let replace__addr_verifast_specific executions ir =
  let (addrs,executions) = List.fold executions ~init:([],[])
      ~f:(fun (addrs,executions) execution ->
          let (addrs,assumptions) = 
          List.fold execution ~init:(addrs,[]) ~f:(fun (addrs,assumptions) assumption ->
              match assumption with
              | {v=Bop (Eq,{v=Id vname;t=_},
                        {v=Id addr;t=_});t=_}
                when String.equal (vname ^ "_addr") addr -> ((vname,addr)::addrs,assumptions)
              | _ -> (addrs, assumption::assumptions))
          in
          (addrs,assumptions::executions))
  in
  let executions = List.map (List.rev executions)
      ~f:(List.map ~f:replace__addr_with_prefixed_var)
  in
  let deal_with_addrs sttmt =
    List.fold addrs
      ~init:(replace__addr_with_prefixed_var
               sttmt)
      ~f:(fun st (vname,addr) ->
          replace_term_in_tterm (Id addr) (Id vname) st)
  in
  let ir =
    {ir with
     tip_call =
       {ir.tip_call with
        results = List.map ir.tip_call.results ~f:(fun rez ->
            {rez with ret_val=deal_with_addrs rez.ret_val})}}
  in
  (List.map executions
    ~f:(fun execution ->
        List.fold addrs ~init:execution ~f:(fun execution (vname,addr) ->
             replace_term_in_tterms (Id addr) (Id vname) execution)),
   ir)

let get_verifast_dummy_variables executions =
  List.join
    (List.map executions
       ~f:(fun execution ->
           (List.join (List.map execution
                         ~f:(collect_nodes (function
                             | {v=Id x;t} when
                                 String.is_prefix x ~prefix:"dummy" ->
                               Some x
                             | _ -> None))))))

let get_vars assumptions result ret_name =
  let output_vars = prepare_output_vars result ret_name in
  (* TODO: here I should really take all the vars mentioned in the trace history,
     excluding the vars in the tip output *)
  let (_,bound_vars) = take_relevant assumptions (String.Set.to_list output_vars) in
  printf "bound vars:\n";
  List.iter bound_vars ~f:(fun v -> printf "%s\n" v);
  let output_params = prepare_output_params result in
  let (_,output_params) = take_relevant assumptions (String.Set.to_list output_params) in
  (output_vars,
   Set.diff (String.Set.of_list output_params) (String.Set.of_list bound_vars))

let find_assignments assertion free_vars =
  [assertion] (*TODO*)

let are_assignments_justified assignments assumptions =
  let (_,justified) =
    List.fold assignments ~init:(assumptions,true)
      ~f:(fun (assumptions,justified) assignment ->
          if justified then
            (assignment::assumptions,
             (Z3_query.is_assignment_justified assignment assumptions))
          else (assumptions,false))
  in
  justified

let induce_assignments_for_exec fixpoints assumptions result ret_name ret_type =
  let assertion_list = (prepare_assertions result ret_name ret_type) |>
                       canonicalize fixpoints
  in
  let (output_vars,free_vars) = get_vars assumptions result ret_name in
  let (_,_,unjustified_assertion) = List.fold assertion_list
      ~init:([],free_vars,None)
      ~f:(fun (assignments,free_vars,unjustified_assertion) assertion ->
          match unjustified_assertion with
          | Some _ -> (assignments,free_vars,unjustified_assertion)
          | None ->
            printf "free vars: \n";
            List.iter (Set.to_list free_vars) ~f:(fun v ->
              printf "%s\n" v);
            let new_assignments = find_assignments assertion free_vars in
            if (are_assignments_justified new_assignments (assignments@assumptions)) then
              let assignments = new_assignments@assignments in
              let (_,bound_vars) = take_relevant (assignments@assumptions) (String.Set.to_list output_vars) in
              let free_vars = Set.diff free_vars (String.Set.of_list bound_vars) in
              if (Z3_query.is_assertion_justified
                    assertion (assumptions@assignments)) then
                (assignments,free_vars,None)
              else
                (assignments,free_vars,Some assertion)
            else (assignments,free_vars,Some assertion))
  in
  unjustified_assertion


let induce_symbolic_assignments fixpoints ir executions =
  let (executions,ir) = replace__addr_verifast_specific executions ir in
  let (_,unjustified_assertion) = List.fold ir.tip_call.results
      ~init:(executions,None)
      ~f:(fun (executions,unjustified_assertion) result->
          match unjustified_assertion with
          | Some _ -> ([],unjustified_assertion)
          | None -> begin match executions with
              | [] -> failwith ("The number of executions must " ^
                                "match the number of tip call results")
              | hd :: tl -> (tl,
                             induce_assignments_for_exec
                               fixpoints hd result
                               ir.tip_call.context.ret_name
                               ir.tip_call.context.ret_type)
            end)
  in
  match unjustified_assertion with
  | Some assertion ->
    Printf.printf "unable find assignments for this to hold: %s\n"
      (render_tterm assertion);
    false
  | None -> true

(* let induce_symbolic_assignments fixpoints ir executions = *)
(*   start_log (); *)
(*   let executions = replace__addr_verifast_specific executions in *)
(*   let fr_var_names = *)
(*     (List.map (String.Map.data ir.free_vars) *)
(*        ~f:(fun spec -> spec.name)) @ *)
(*     (match ir.tip_call.context.ret_name with *)
(*      | Some name -> [name] *)
(*      | None -> []) *)
(*   in *)
(*   lprintf "free vars: \n"; *)
(*   lprint_list fr_var_names; *)
(*   let assertion_lists = List.map ir.tip_call.results ~f:(fun result -> *)
(*       (prepare_assertions result *)
(*          ir.tip_call.context.ret_name *)
(*          ir.tip_call.context.ret_type) |> *)
(*       canonicalize fixpoints) *)
(*   in *)
(*   let assignments = List.fold assertion_lists ~init:[] *)
(*       ~f:(fun assignments assertions -> *)
(*           lprintf "working with assertions:\n"; *)
(*           lprint_list (List.map assertions ~f:render_tterm); *)
(*           List.fold executions ~init:assignments *)
(*             ~f:(fun assignments assumptions -> *)
(*                 let vars = String.Set.to_list *)
(*                     (String.Set.diff (String.Set.of_list fr_var_names) *)
(*                        (String.Set.of_list (List.map assignments ~f:fst))) *)
(*                 in *)
(*                 let var_ids = List.map vars ~f:(fun name -> Id name) in *)
(*                 let assumptions = assumptions |> simplify fixpoints var_ids *)
(*                 in *)
(*                 lprintf "\nassuming assignments:\n"; *)
(*                 lprint_list (List.map assignments *)
(*                                ~f:(fun a -> (fst a) ^ " = " ^ *)
(*                                             (render_term (snd a)))); *)
(*                 lprintf "\nworking with assumptions:\n"; *)
(*                 lprint_list (List.map assumptions ~f:render_tterm); *)
(*                 lprintf "\n|-|-|- vars:\n"; *)
(*                 lprint_list vars; *)
(*                 assignments@(guess_assignments assumptions assertions vars))) *)
(*   in *)
(*   lprintf "\n\n JUSTIFYING \n\n"; *)
(*   let justified_assignments = List.filter assignments ~f:(fun (var,value) -> *)
(*       is_assignment_justified fixpoints var value executions) *)
(*   in *)
(*   apply_assignments justified_assignments ir; *)
