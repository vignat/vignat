open Core.Std
open Ir

let rec render_eq_sttmt ~is_assert out_arg (out_val:tterm) =
  let head = (if is_assert then "assert" else "assume") in
  match out_val.v with
  | Struct (_, fields) ->
    (*TODO: check that the types of Str (_,fts)
      are the same as in fields*)
    String.concat (List.map fields ~f:(fun {name;value} ->
        render_eq_sttmt ~is_assert {v=Str_idx (out_arg, name);t=Unknown} value))
  | _ -> "//@ " ^ head ^ "(" ^ (render_tterm out_arg) ^ " == " ^
         (render_tterm out_val) ^ ");\n"

let render_fcall_with_lemmas context =
  (String.concat ~sep:"\n" context.pre_lemmas) ^ "\n" ^
  (match context.ret_name with
   | Some name -> (ttype_to_str context.ret_type) ^
                  " " ^ name ^ " = "
   | None -> "") ^
  (render_term context.application) ^ ";\n" ^
  (String.concat ~sep:"\n" context.post_lemmas) ^ "\n"

let render_args_post_conditions ~is_assert apk =
  (String.concat ~sep:"\n" (List.map apk
                              ~f:(fun {lhs;rhs;} ->
                                  render_eq_sttmt ~is_assert
                                    lhs rhs)))

let render_post_assumptions post_statements =
  (String.concat ~sep:"\n" (List.map post_statements
                              ~f:(fun t ->
                                  "/*@ assume(" ^
                                  (render_tterm t) ^
                                  ");@*/")))

let render_tip_post_sttmts {args_post_conditions;
                            ret_val=_;post_statements} =
  ""
(* (render_post_assumptions post_statements) ^ "\n" ^ *)
(* (render_args_post_conditions ~is_assert:true args_post_conditions) *)

let render_ret_equ_sttmt ~is_assert ret_name ret_val =
  match ret_name with
  | Some name -> (render_eq_sttmt ~is_assert {v=Id name;t=Unknown} ret_val) ^ "\n"
  | None -> "\n"

let rec render_assignment {lhs;rhs;} =
  match rhs.v with
  | Struct (_, fvals) ->
    String.concat ~sep: "\n"
      (List.map fvals
         ~f:(fun {name;value} ->
             render_assignment
               {lhs={v=Str_idx (lhs, name);t=Unknown};
                rhs=value;}))
  | Undef -> "";
  | _ -> (render_tterm lhs) ^ " = " ^ (render_tterm rhs) ^ ";"

let render_extra_pre_conditions context =
  String.concat ~sep:"\n"
    (List.map context.extra_pre_conditions ~f:(fun eq_cond ->
         (render_assignment eq_cond)))

let render_hist_fun_call {context;result} =
  (render_extra_pre_conditions context) ^
  (render_fcall_with_lemmas context) ^
  (render_args_post_conditions ~is_assert:false result.args_post_conditions) ^
  match result.ret_val.t with
  | Ptr _ -> (if result.ret_val.v = Zeroptr then
                "//@ assume(" ^ (Option.value_exn context.ret_name) ^
                " == " ^ "0);\n"
              else
                "//@ assume(" ^ (Option.value_exn context.ret_name) ^
                " != " ^ "0);\n") ^
             "/* Do not render the return ptee assumption for hist calls */\n"
  | _ -> render_ret_equ_sttmt ~is_assert:false context.ret_name result.ret_val

let find_known_complementaries (sttmts:tterm list) =
  List.filter_map sttmts ~f:(fun sttmt ->
      match sttmt.v with
      | Bop (Eq,{v=Bool false;t=_},rhs) -> Some (sttmt,rhs)
      | Bop (Eq,{v=Int 0;t=_}, rhs) -> Some (sttmt,rhs)
      | _ -> None)

let find_complementary_sttmts sttmts1 sttmts2 =
  let find_from_left sttmts1 (sttmts2:tterm list) =
    List.find_map (find_known_complementaries sttmts1) ~f:(fun (orig,complement) ->
        if List.exists sttmts2 ~f:(fun sttmt2 -> term_eq complement.v sttmt2.v) then
          Some (orig,complement)
        else None)
  in
  match find_from_left sttmts1 sttmts2 with
  | Some (st1,st2) -> Some (st1,st2)
  | None -> find_from_left sttmts2 sttmts1

let rec gen_plain_equalities {lhs;rhs} =
  match rhs.t, rhs.v with
  | Ptr ptee_t, Addr pointee ->
    gen_plain_equalities {lhs={v=Deref lhs;t=ptee_t};
                          rhs=pointee}
  | Str (_, fields), Struct (_, fvals) ->
    List.join
      (List.map fields ~f:(fun (name,ttype) ->
           let v = List.find_exn fvals ~f:(fun {name=vname;value} ->
               String.equal vname name)
           in
           gen_plain_equalities
             {lhs={v=Str_idx (lhs, name);t=ttype};
              rhs=v.value}))
  | Str (_, fields), _ ->
    List.join
      (List.map fields ~f:(fun (name,ttype) ->
           gen_plain_equalities
             {lhs={v=Str_idx (lhs, name);t=ttype};
              rhs={v=Str_idx (rhs, name);t=ttype}}))
  | Uint64, Int _
  | Sint32, Int _
  | Sint32, Bop (Add, {v=Id _;t=_}, {v=Int _; t=_})
  | Sint8, Int _
  | Uint32, Int _
  | Uint32, Str_idx _
  | Uint16, Int _
  | Uint16, Str_idx _
  | Uint8, Int _
  | Uint8, Str_idx _
  | Sint32, Id _
  | Sint8, Id _
  | Uint64, Id _
  | Uint32, Id _
  | Uint16, Id _
  | Uint8, Id _
  | Boolean, Id _
  | Boolean, Bool _
  | Ptr _, Id _
  | Ptr _, Int _ -> [{lhs;rhs}]
  | Boolean, Int 0 ->
    [{lhs;rhs={v=Bool false;
               t=Boolean}}]
  | Boolean, Int 1 ->
    [{lhs;rhs={v=Bool true;
               t=Boolean}}]
  | Boolean, Int x ->
    [{lhs;rhs={v=Not {v=Bop (Eq, {v=Int x;t=Sint32},
                             {v=Int 0;t=Sint32});
                      t=Boolean};
               t=Boolean}}]
  | Uint16, Cast (Uint16, {v=Id _;t=_}) -> [{lhs;rhs}]
  | Ptr _, Zeroptr -> []
  | _ -> failwith ("unsupported output type: " ^
                   (ttype_to_str rhs.t) ^
                   " : " ^
                   (render_tterm rhs))


let gen_ret_equalities ret_val ret_name ret_type =
  match ret_name with
  | Some ret_name ->
    gen_plain_equalities {lhs={v=Id ret_name;t=ret_type};rhs=ret_val}
  | None -> []

let make_assignments_for_eqs equalities =
  List.map equalities ~f:(fun {lhs;rhs} ->
      {lhs=rhs;rhs=lhs})

let split_assignments assignments =
  List.fold assignments ~init:([],[]) ~f:(fun (concrete,symbolic) assignment ->
      match assignment.lhs.v with
      | Cast (_,{v=Id _;t=_})
      | Id _ -> (concrete,assignment::symbolic)
      | Int _ -> (assignment::concrete,symbolic)
      | Bool _ -> (assignment::concrete,symbolic)
      | Bop (Add, ({v=Id _;t=_} as symb), ({v=Int x;t=_} as delta)) ->
        (concrete,
         {lhs=symb;
          rhs={v=Bop (Sub, assignment.rhs, delta);
               t=assignment.rhs.t}}::
         symbolic)
      | Struct (_, []) -> (* printf "skipping empty assignment: %s = %s" *)
        (*  (render_tterm assignment.lhs) *)
        (*  (render_tterm assignment.rhs); *)
        (concrete,symbolic)
      | Str_idx _ -> (assignment::concrete,symbolic)
      | _ -> failwith ("unsupported assignment in split_assignments: " ^
                       (render_tterm assignment.lhs) ^
                       " = " ^ (render_tterm assignment.rhs)))

let apply_assignments assignments terms =
  List.fold assignments ~init:terms ~f:(fun terms {lhs;rhs} ->
      List.map terms ~f:(replace_term_in_tterm lhs.v rhs.v))

let render_assumptions assumptions  =
  String.concat ~sep:"\n" (List.map assumptions ~f:(fun t ->
      "//@ assume(" ^ (match t.v with
      | Id x -> "0 != " ^ x
      | Bop (Bit_and,_,_) -> "0 != " ^ (render_tterm t)
      | _ -> (render_tterm t)) ^
      ");")) ^ "\n"

let render_input_assumptions terms =
  render_assumptions terms

let ids_from_term term =
  String.Set.of_list
    (collect_nodes (function
         | {v=Id name;t=_} -> Some name
         | _ -> None)
        term)

let ids_from_terms terms =
  List.fold terms ~init:String.Set.empty ~f:(fun ids term ->
      String.Set.union ids (ids_from_term term))

let ids_from_eq_conditions eq_conds =
  List.fold eq_conds ~init:String.Set.empty ~f:(fun ids cond ->
      String.Set.union (ids_from_term cond.lhs)
        (String.Set.union (ids_from_term cond.rhs) ids))

let split_constraints tterms symbols =
  List.partition_tf tterms ~f:(fun tterm ->
      Set.for_all (ids_from_term tterm) ~f:(String.Set.mem symbols))

let render_some_assignments_as_assumptions assignments =
  String.concat ~sep:"\n" (List.map assignments ~f:(fun {lhs;rhs} ->
      match lhs,rhs with
      | {v=Id _;t=_},{v=Id _;t=_} ->
        "//@ assume(" ^ (render_tterm lhs) ^ " == " ^ (render_tterm rhs) ^ ");"
      | _ -> "//skip this assume: " ^ (render_tterm lhs) ^ " == " ^
             (render_tterm rhs) ^ " -- too complicated"))

let render_concrete_assignments_as_assertions assignments =
  String.concat ~sep:"\n"
    (List.map assignments ~f:(fun {lhs;rhs} ->
         match rhs.t with
         | Ptr _ ->
           "/*@ assert(" ^ (render_tterm rhs) ^ " == " ^
           (render_tterm lhs) ^ "); @*/"
         | _ ->
           "/*@ assert(" ^ (render_tterm lhs) ^ " == " ^
           (render_tterm rhs) ^ "); @*/"))

let expand_conjunctions terms =
  let rec expand_tterm tterm =
    match tterm with
    | {v=Bop (And, t1, t2);t=_} -> (expand_tterm t1) @ (expand_tterm t2)
    | tterm -> [tterm]
  in
  List.join (List.map terms ~f:expand_tterm)

let guess_support_assignments constraints symbs =
  let (assignments,_) =
    List.fold constraints ~init:([],symbs) ~f:(fun (assignments,symbs) tterm ->
        match tterm.v with
        | Bop (Eq, {v=Id x;t}, rhs) when String.Set.mem symbs x ->
          ({lhs={v=Id x;t};rhs}::assignments, String.Set.remove symbs x)
        | Bop (Eq, lhs, {v=Id x;t}) when String.Set.mem symbs x ->
          ({lhs={v=Id x;t};rhs=lhs}::assignments, String.Set.remove symbs x)
        | Bop (Le, lhs, {v=Id x;t}) when String.Set.mem symbs x ->
          ({lhs={v=Id x;t};rhs=lhs}::assignments, String.Set.remove symbs x)
        | Bop (Le, {v=Id x;t}, rhs) when String.Set.mem symbs x ->
          ({lhs={v=Id x;t};rhs}::assignments, String.Set.remove symbs x)
        | _ -> (assignments, symbs))
  in
  assignments


let render_output_check
    ret_val ret_name ret_type model_constraints
    hist_symbs args_post_conditions
  =
  let (input_constraints,output_constraints) =
    split_constraints model_constraints hist_symbs
  in
  let ret_equalities = gen_ret_equalities ret_val ret_name ret_type
  in
  let args_equalities =
    List.join (List.map args_post_conditions ~f:gen_plain_equalities)
  in
  let assignments = make_assignments_for_eqs (ret_equalities@args_equalities)
  in
  let output_constraints = expand_conjunctions output_constraints in
  let output_symbs = ids_from_eq_conditions assignments in
  let unalloc_symbs = String.Set.diff
      (String.Set.diff
         (ids_from_terms output_constraints)
         output_symbs)
      hist_symbs
  in
  let support_assignments =
    guess_support_assignments output_constraints unalloc_symbs
  in
  let assignments = assignments@support_assignments in
  let (concrete_assignments,
       symbolic_var_assignments) = split_assignments assignments
  in
  let upd_model_constraints =
    apply_assignments symbolic_var_assignments output_constraints
  in
  "// Output check\n" ^
  (render_input_assumptions input_constraints) ^ "\n" ^
  (* VV For the "if (...)" condition, which involves
     VV the original value (non-renamed)*)
  (render_some_assignments_as_assumptions symbolic_var_assignments) ^ "\n" ^
  (render_concrete_assignments_as_assertions concrete_assignments) ^ "\n" ^
  (String.concat ~sep:"\n"
     (List.map upd_model_constraints ~f:(fun constr ->
          "/*@ assert(" ^ (render_tterm constr) ^ "); @*/")))

let tterm_list_to_string tterms =
  String.concat ~sep:"\n" (List.map tterms ~f:render_tterm)

type decision_tree = Single_result of Ir.tip_result
                   | Alternative_by_ret of
                       ((Ir.tterm*decision_tree)*(Ir.tterm*decision_tree))
                   | Alternative_by_constraint of
                       ((Ir.tterm*decision_tree)*(Ir.tterm*decision_tree))

let statements_aligned_with_constraint constr sttmts =
  List.exists sttmts ~f:(fun sttmt ->
      match sttmt.v, constr.v with
      | Bop (Bit_and,x,_), _ when (term_eq x.v constr.v) -> true
      | Bop (Eq,{v=Int x;t=_},y),Bop (Eq,{v=Bool false;t=_},{v=Bop (Eq,{v=Int z;t=_},w);t=_})
        when (term_eq y.v w.v) && x <> z ->
        true
      | _ -> term_eq constr.v sttmt.v)

let one_sttmt_list_is_subset_of_another sttmts1 sttmts2 =
  let is_subset sttmts1 sttmts2 =
    List.for_all sttmts1 ~f:(fun sttmt1 ->
      List.exists sttmts2 ~f:(fun sttmt2 -> term_eq sttmt1.v sttmt2.v))
  in
  if is_subset sttmts1 sttmts2 then Some `first
  else if is_subset sttmts2 sttmts1 then Some `second
  else None

let rec build_decision_tree results =
  match results with
  | [] -> failwith "There must be at least one tip-call result"
  | hd :: [] -> Single_result hd
  | hd1 :: hd2 :: tl ->
    if term_eq hd1.ret_val.v hd2.ret_val.v then
      match find_complementary_sttmts
              hd1.post_statements
              hd2.post_statements with
      | None -> begin match one_sttmt_list_is_subset_of_another
                              hd1.post_statements hd2.post_statements with
        | Some `first -> build_decision_tree (hd2 :: tl)
        | Some `second -> build_decision_tree (hd1 :: tl)
        | None ->
          printf "Failed to differentiate tip-call results:\n%s\nVS\n%s\n"
            (tterm_list_to_string hd1.post_statements)
            (tterm_list_to_string hd2.post_statements);
        failwith ("Can not differentiate tip-call results.")
        end
      | Some (sttmt1,sttmt2) ->
        let results_pro1 = List.filter results ~f:(fun res ->
            statements_aligned_with_constraint sttmt1 res.post_statements)
        in
        let results_pro2 = List.filter results ~f:(fun res ->
            statements_aligned_with_constraint sttmt2 res.post_statements)
        in
      assert (0 < List.length results_pro1);
      assert (0 < List.length results_pro2);
      if (List.length results_pro1) + (List.length results_pro2) <>
         (List.length results) then
        failwith ("Statements " ^ (render_tterm sttmt1) ^ " and " ^
                  (render_tterm sttmt2) ^
                  " do not cleanly divide results set. Leftover " ^
                  "post statements: \n" ^
                  (String.concat ~sep:" \n AND \n "
                     (List.map (List.filter results ~f:(fun res ->
                          not (statements_aligned_with_constraint
                                 sttmt1 res.post_statements) &&
                          not (statements_aligned_with_constraint
                                 sttmt2 res.post_statements)))
                         ~f:(fun res -> tterm_list_to_string res.post_statements))));
        Alternative_by_constraint ((sttmt1, build_decision_tree results_pro1),
                                   (sttmt2, build_decision_tree results_pro2))
    else
      let results_pro1 = List.filter results ~f:(fun res ->
        term_eq res.ret_val.v hd1.ret_val.v) in
      let results_pro2 = List.filter results ~f:(fun res ->
        term_eq res.ret_val.v hd2.ret_val.v) in
      assert (0 < List.length results_pro1);
      assert (0 < List.length results_pro2);
      assert ((List.length results_pro1) + (List.length results_pro2) =
              (List.length results));
      Alternative_by_ret ((hd1.ret_val, build_decision_tree results_pro1),
                          (hd2.ret_val, build_decision_tree results_pro2))

let rec render_post_assertions dtree ret_name ret_type hist_symbs =
  match dtree with
  | Single_result res ->
    (render_output_check
       res.ret_val ret_name ret_type
       res.post_statements hist_symbs
       res.args_post_conditions) ^ "\n"
  | Alternative_by_constraint ((sttmt1,dtree1),
                               (sttmt2,dtree2)) ->
    "if (" ^ (render_tterm sttmt1) ^ ") {\n" ^
    (render_post_assertions dtree1 ret_name ret_type hist_symbs) ^
    "} else {\n" ^
    (render_post_assertions dtree2 ret_name ret_type hist_symbs) ^
    "}\n"
  | Alternative_by_ret ((ret1,dtree1),(ret2,dtree2)) ->
    let rname = match ret_name with
      | Some n -> n
      | None -> failwith ("When two tip-call results are " ^
                          " differentiated by ret value:" ^
                          (render_tterm ret1) ^ " vs. " ^
                          (render_tterm ret2) ^ ", the ret name" ^
                          " must be present.")
    in
    "if (" ^ rname ^ " == " ^ (render_tterm ret1) ^ ") {\n" ^
    (render_post_assertions dtree1 ret_name ret_type hist_symbs) ^
    "} else {\n " ^
    (render_post_assertions dtree2 ret_name ret_type hist_symbs) ^
    "}"

let render_export_point name =
  "int " ^ name ^ ";\n"

let render_assignments args =
  String.concat ~sep:"\n"
    (List.map args ~f:(fun arg ->
         render_assignment {lhs={v=Id arg.name;t=Unknown;};
                            rhs=arg.value}))

let render_equality_assumptions args =
  String.concat ~sep:"\n"
    (List.map (String.Map.data args) ~f:(fun arg ->
         match arg.value.v with
         | Undef -> ""
         | _ -> "//@ assume(" ^ arg.name ^ " == "
                ^ (render_tterm arg.value) ^ ");"))

let render_tip_fun_call
    {context;results} export_point free_vars hist_symbols ~render_assertions =
  (render_fcall_with_lemmas context) ^
  (* "// The legibility of these assignments is ensured by analysis.ml\n" ^ *)
  (* (render_equality_assumptions free_vars) ^ "\n" ^ *)
  (render_export_point export_point) ^
  (if render_assertions then
     let dtree = build_decision_tree
         (List.sort ~cmp:(fun res1 res2 ->
              (List.length res1.post_statements) -
              (List.length res2.post_statements))
         results) in
     render_post_assertions dtree context.ret_name context.ret_type hist_symbols
   else
     "")

let render_semantic_checks semantic_checks =
  if (String.equal semantic_checks "") then
    "\n// No semantic checks for this trace\n"
  else
    "\n// Semantics checks (rendered before the final call,\n" ^
    "// because the final call should be the invariant_consume)\n" ^
    "/*@ {\n" ^ semantic_checks ^ "\n} @*/\n"


let render_vars_declarations ( vars : var_spec list ) =
  String.concat ~sep:"\n"
    (List.map vars ~f:(fun v ->
         match v.value.t with
         | Unknown | Sunknown | Uunknown ->
           "//" ^ ttype_to_str v.value.t ^ " " ^ v.name ^ ";"
         | _ ->
           ttype_to_str v.value.t ^ " " ^ v.name ^ ";")) ^ "\n"

let render_hist_calls hist_funs =
  String.concat ~sep:"\n" (List.map hist_funs ~f:render_hist_fun_call)

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

let render_context_assumptions assumptions  =
  render_assumptions assumptions

let render_allocated_args args =
  String.concat ~sep:"\n"
    (List.map args
       ~f:(fun spec -> (ttype_to_str spec.value.t) ^ " " ^
                       (spec.name) ^ ";")) ^ "\n"

let render_final finishing ~catch_leaks =
  if finishing && catch_leaks then
    "/* This sequence must terminate cleanly: no need for assume(false); */\n"
  else
    "//@ assume(false);\n"

let get_all_symbols calls =
  List.fold calls ~init:String.Set.empty ~f:(fun symbols call ->
      String.Set.union (ids_from_term call.result.ret_val)
        (String.Set.union (ids_from_eq_conditions call.result.args_post_conditions)
           (String.Set.union (ids_from_eq_conditions call.context.extra_pre_conditions)
              (String.Set.union (ids_from_term {v=call.context.application;t=Unknown})
                 (match call.context.ret_name with
                  | Some name -> (String.Set.add symbols name)
                  | None -> symbols)))))

(* let get_some_input_assumptions {context=_;results} hist_symbs = *)
(*   match results with *)
(*   | result::[] -> *)
(*     let (input_constraints,_) = *)
(*       split_constraints result.post_statements hist_symbs *)
(*     in *)
(*     input_constraints *)
(*   | res1::res2::[] -> *)
(*     [] *)
(*   | _ -> failwith "Unsupported number of results (> 2)." *)

let render_ir ir fout ~render_assertions =
  let hist_symbols = get_all_symbols ir.hist_calls in
  (* let tip_input_assumptions = *)
  (*   get_some_input_assumptions ir.tip_call hist_symbols *)
  (* in *)
  Out_channel.with_file fout ~f:(fun cout ->
      Out_channel.output_string cout ir.preamble;
      Out_channel.output_string cout (render_cmplexes ir.cmplxs);
      Out_channel.output_string cout (render_vars_declarations
                                        (String.Map.data ir.free_vars));
      Out_channel.output_string cout (render_allocated_args ir.arguments);
      Out_channel.output_string cout (render_context_assumptions
                                        ir.context_assumptions);
      (* Out_channel.output_string cout (render_context_assumptions *)
      (*                                   tip_input_assumptions); *)
      Out_channel.output_string cout (render_tmps ir.tmps);
      Out_channel.output_string cout (render_assignments ir.arguments);
      Out_channel.output_string cout (render_hist_calls ir.hist_calls);
      Out_channel.output_string cout (render_semantic_checks ir.semantic_checks);
      Out_channel.output_string cout (render_tip_fun_call
                                        ir.tip_call ir.export_point
                                        ir.free_vars
                                        hist_symbols
                                        ~render_assertions);
      Out_channel.output_string cout (render_final ir.finishing
                                        ~catch_leaks:render_assertions);
      Out_channel.output_string cout "}\n")
