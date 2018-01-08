open Core
open Ir

let do_log = true

let log str =
  if do_log then Out_channel.with_file ~append:true "analysis.log" ~f:(fun f ->
      Out_channel.output_string f str)
  else ()

let start_log () =
  if do_log then Out_channel.with_file "analysis.log" ~f:(fun _ -> ())
  else ()

let lprintf fmt = ksprintf log fmt

let lprint_list lst =
  List.iter lst ~f:(fun vn -> lprintf "%s\n" vn)

let expand_fixpoints_in_tterm
    (fixpoints : Ir.tterm Core.String.Map.t) tterm =
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
  call_recursively_on_term impl tterm

let expand_fixpoints fixpoints sttmts =
  List.map sttmts ~f:(expand_fixpoints_in_tterm fixpoints)

let remove_trues sttmts =
  List.filter sttmts ~f:(function {v=Bool true;t=_} -> false | _ -> true)

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

let remove_double_negation sttmt =
  sttmt |> call_recursively_on_term (fun term ->
      match term with
      | Not {v=Not tt;t=_} -> Some tt.v
      | _ -> None)

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

let reduce_struct_idxes sttmt =
  sttmt |> call_recursively_on_term (function
      | Str_idx ({v=Struct(_,fields);t=_}, field) ->
        Some (List.find_exn fields ~f:(fun {name;value=_} ->
          name = field)).value.v
      | _ -> None)

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

let apply_assignments assignments terms =
  List.fold assignments ~init:terms ~f:(fun terms {lhs;rhs} ->
    List.map terms ~f:(replace_term_in_tterm lhs.v rhs.v))

let make_assignments_for_eqs equalities =
  List.map equalities ~f:(fun {lhs;rhs} ->
      {lhs=rhs;rhs=lhs})

let are_symbolic_assignments_justified
    spec_constraints assignments model_constraints =
  let updated_model_constraints =
    apply_assignments assignments model_constraints
  in
  List.for_all updated_model_constraints
    ~f:(fun model_constraint ->
        lprintf "Checking constraint: %s\n" (render_tterm model_constraint);
        Z3_query.check_implication spec_constraints model_constraint)

let gen_eq_for_assignment assignment =
  {t=Boolean;v=Bop (Eq, assignment.lhs, assignment.rhs)}

let are_concrete_assignments_justified spec_constraints assignments =
  List.for_all assignments ~f:(fun assignment ->
      lprintf "Checking concrete assignment: %s = %s\n"
        (render_tterm assignment.lhs)
        (render_tterm assignment.rhs);
      Z3_query.check_implication
        spec_constraints (gen_eq_for_assignment assignment))

let split_assignments assignments =
  List.fold assignments ~init:([],[]) ~f:(fun (concrete,symbolic) assignment ->
      match assignment.lhs.v with
      | Id _ -> (concrete,assignment::symbolic)
      | Int _ -> (assignment::concrete,symbolic)
      | Struct (_, []) -> lprintf "skipping empty assignment: %s = %s"
                           (render_tterm assignment.lhs)
                           (render_tterm assignment.rhs);
        (concrete,symbolic)
      | _ -> failwith ("unsupported assignment: " ^
                       (render_tterm assignment.lhs) ^
                       " = " ^ (render_tterm assignment.rhs)))

let is_execution_justified
    model_variables model_constraints
    spec_constraints model_spec_equalities =
  let assignments = make_assignments_for_eqs model_spec_equalities
  in
  lprintf "Trying these assignments: \n";
  lprint_list (List.map assignments ~f:(fun {lhs;rhs} ->
      (render_tterm lhs) ^ " = " ^ (render_tterm rhs)));
  let are_assignments_justified assignments =
    let (concrete_assignments,
         symbolic_var_assignments) = split_assignments assignments
    in
    (are_concrete_assignments_justified
       spec_constraints concrete_assignments) &&
    (are_symbolic_assignments_justified
       spec_constraints symbolic_var_assignments model_constraints)
  in
  are_assignments_justified assignments

let gen_ret_equalities ret_val ret_name ret_type =
  match ret_name with
  | Some ret_name -> begin
      match ret_type, ret_val.v with
      | Ptr (Str (_, fields)), Addr {v=Struct (_, fvals);t=_} ->
        List.map fields ~f:(fun (name,ttype) ->
            let v = List.find_exn fvals ~f:(fun {name=vname;value} ->
                String.equal vname name)
            in
            {lhs={v=Str_idx ({v=Id ret_name;t=ret_type}, name);t=ttype};
             rhs=v.value})
      | Sint32, Int _
      | Sint8, Int _
      | Uint32, Int _
      | Uint16, Int _
      | Uint8, Int _
      | Sint32, Id _
      | Sint8, Id _
      | Uint32, Id _
      | Uint16, Id _
      | Uint8, Id _
        -> [{lhs={v=Id ret_name;t=ret_type};rhs=ret_val}]
      | Ptr (Uint16), Addr ({v=Id x;t})
        ->
        [{lhs={v=Id x;t};rhs={v=Deref {v=Id ret_name;t=ret_type};t}}]
      | _ -> failwith ("unsupported return type: " ^
                       (ttype_to_str ret_type) ^
                       " : " ^
                       (render_tterm ret_val))
      end
  | None -> []

let ids_from_term term =
  String.Set.of_list
    (collect_nodes (function
         | {v=Id name;t=_} -> Some name
         | _ -> None)
        term)

let ids_from_terms terms =
  List.fold terms ~init:String.Set.empty ~f:(fun ids term ->
    String.Set.union ids (ids_from_term term))

let var_names free_vars =
  String.Set.of_list
    (List.map (String.Map.data free_vars) ~f:(fun {name; value=_} -> name))

let get_output_variables equalities =
  String.Set.of_list
    (List.filter_map equalities ~f:(fun {lhs=_;rhs} ->
         match rhs.v with
         | Id name -> Some name
         | _ -> None))

let get_free_vars_set ir =
  String.Set.of_list
    (List.map (String.Map.data ir.free_vars) ~f:(fun {name;value=_} -> name))

let induce_symbolic_assignments fixpoints ir (spec_constraintss : tterm list list) =
  start_log();
  assert(not (List.is_empty ir.tip_call.results));
  assert(not (List.is_empty spec_constraintss));
  List.for_all spec_constraintss ~f:(fun spec_constraints ->
      List.exists ir.tip_call.results ~f:(fun result ->
          let model_constraints = result.post_statements
          in
          let equalities = (gen_ret_equalities
                              result.ret_val ir.tip_call.context.ret_name
                              ir.tip_call.context.ret_type) @
                           result.args_post_conditions
          in
          let model_variables = get_output_variables equalities
          in
          let free_vars = get_free_vars_set ir in
          assert(String.Set.subset model_variables free_vars);
          is_execution_justified
            model_variables model_constraints
            spec_constraints equalities))
