open Core
open Ir

let rec render_eq_sttmt ~is_assert out_arg (out_val:tterm) =
  let head = (if is_assert then "assert" else "assume") in
  (*printf "render_eq_sttmt %s %s --- %s %s\n" (render_tterm out_arg) (ttype_to_str out_arg.t) (render_tterm out_val) (ttype_to_str out_val.t);*)
  match out_val.v, out_val.t with
  (* A struct and its first member have the same address... oh and this is a hack so let's support doubly-nested structs *)
  | Id ovid, Uint16 ->
    begin match out_arg.v, out_arg.t with
      | Id oaid, Str (_, (outerfname,Str(_,(fname,_)::_))::_) -> "//@ " ^ head ^ "(" ^ oaid ^ "." ^ outerfname ^ "." ^ fname ^ " == " ^ ovid ^ ");\n"
      | Id oaid, Str (_, (fname,_)::_) -> "//@ " ^ head ^ "(" ^ oaid ^ "." ^ fname ^ " == " ^ ovid ^ ");\n"
      | _, _ -> "//@ " ^ head ^ "(" ^ (render_tterm out_arg) ^ " == " ^ (render_tterm out_val) ^ ");\n"
    end
  | Id ovid, Ptr _ -> (* HUGE HACK assume the type is wrongly guessed and it's actually an integer *)
      render_eq_sttmt ~is_assert:is_assert out_arg {v=out_val.v;t=Uint16}
  (* Don't use == over structs, VeriFast doesn't understand it and returns a confusing message about dereferencing pointers *)
  | Id ovid, Str (_, ovfields) ->
    begin match out_arg.v, out_arg.t with
    | Id oaid, Ptr oat -> (* HUGE HACK assume the type is wrongly guessed and it's actually an integer *)
      render_eq_sttmt ~is_assert:is_assert out_val {v=out_arg.v;t=Uint16}
    | Id oaid, Uint16 ->
      render_eq_sttmt ~is_assert:is_assert out_val out_arg
    | Id oaid, _ ->
      if out_val.t <> out_arg.t then failwith ("not the right type! " ^ ovid ^ ":" ^ (ttype_to_str out_val.t) ^ " <> " ^ oaid ^ ":" ^ (ttype_to_str out_arg.t));
      String.concat (List.map ovfields ~f:(fun (name,_) ->
                       "//@ " ^ head ^ "(" ^ ovid ^ "." ^ name ^ " == " ^ oaid ^ "." ^ name ^ ");\n"))

    | _ -> failwith "not supported, sorry"
    end
  | Addr ptee, _ ->
    begin match out_arg.t with
      | Ptr Void ->
        render_eq_sttmt
          ~is_assert
          {v=Deref {v=Cast (out_val.t, out_arg);t=out_val.t};
           t=get_pointee out_val.t}
          ptee
      | _ ->
        render_eq_sttmt
          ~is_assert
          {v=Deref out_arg;t=get_pointee out_arg.t}
          ptee
    end
  | Struct (_, fields), _ ->
    if out_val.t <> out_arg.t then
      failwith ("arg and val types inconsistent: arg:" ^
                (ttype_to_str out_arg.t) ^ " <> val: " ^
                (ttype_to_str out_val.t));
    (match out_arg with
     | {v=Deref {v=Id arg_name;t=_};t=_} -> "//@ " ^ head ^ "(" ^ arg_name ^ "!= 0 );\n" (* can be important to know the arg can be read *)
     | _ -> "") ^
    String.concat (List.map fields ~f:(fun {name;value} ->
        render_eq_sttmt ~is_assert {v=Str_idx (out_arg, name);t=value.t} value))
  | Undef, _ -> failwith ("// render_eq_sttmt undef for " ^ (render_tterm out_arg))
  | _, _ -> "//@ " ^ head ^ "(" ^ (render_tterm out_arg) ^ " == " ^ (render_tterm out_val) ^ ");\n"

let render_fcall_with_prelemmas context =
  (String.concat ~sep:"\n" context.pre_lemmas) ^ "\n" ^
  (match context.ret_name with
   | Some name -> (ttype_to_str context.ret_type) ^
                  " " ^ name ^ " = "
   | None -> "") ^
  (render_term context.application) ^ ";\n"

let render_postlemmas context =
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

let render_ret_equ_sttmt ~is_assert ret_name ret_type ret_val =
  match ret_name with
  | Some name -> (render_eq_sttmt ~is_assert {v=Id name;t=ret_type} ret_val) ^ "\n"
  | None -> "\n"

let render_assignment {lhs;rhs;} =
  match rhs.v with
  | Undef -> "";
  | _ -> (render_tterm lhs) ^ " = " ^ (render_tterm rhs) ^ ";"

let rec gen_plain_equalities {lhs;rhs} =
  if term_eq lhs.v rhs.v then []
  else match rhs.t, rhs.v with
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
  | Sint64, Str_idx _
  | Sint64, Id _
  | Sint64, Int _
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
  | _, Undef -> []
  | _ -> match lhs.v, rhs.v with
         | Deref lref, Deref rref -> gen_plain_equalities {lhs=lref; rhs=rref}
         | Id x, Deref {v=Addr {v=Id y;t=_};t=_} when x = y -> [{lhs;rhs}]
         | _ -> failwith ("unsupported output type:rhs.t=" ^
                          (ttype_to_str rhs.t) ^
                          " : rhs=" ^
                          (render_tterm rhs) ^
                          " : lhs.t=" ^
                          (ttype_to_str lhs.t) ^
                          " : lhs=" ^
                          (render_tterm lhs))

let gen_plain_equalities_for_all equalities =
  List.join (List.map equalities ~f:gen_plain_equalities)

let render_extra_pre_conditions context =
  String.concat ~sep:"\n"
    (List.map
       (* (gen_plain_equalities_for_all context.extra_pre_conditions)
          ^-- this should be done by now as a byproduct of filtering *)
       context.extra_pre_conditions
       ~f:(fun eq_cond ->
           (render_assignment eq_cond)))

let render_hist_fun_call {context;result} =
  "// PRECONDITIONS\n" ^
  (render_extra_pre_conditions context) ^
  "// PRELEMMAS AND CALL\n" ^
  (render_fcall_with_prelemmas context) ^
  "// RET STUFF\n" ^
  (match result.ret_val.t with
   | Ptr _ -> (if result.ret_val.v = Zeroptr then
                 "//@ assume(" ^ (Option.value_exn context.ret_name) ^
                 " == " ^ "0);\n"
               else
                 "//@ assume(" ^ (Option.value_exn context.ret_name) ^
                 " != " ^ "0);\n") ^
              "/* Do not render the return ptee assumption for hist calls */\n"
   | _ -> render_ret_equ_sttmt ~is_assert:false context.ret_name context.ret_type result.ret_val) ^
  "// POSTLEMMAS\n" ^
  (render_postlemmas context) (* postlemmas can depend on the return value *) ^
  "// POSTCONDITIONS\n" ^
  (render_args_post_conditions ~is_assert:false result.args_post_conditions) (* ret can influence whether args are accessible *)

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
      | Deref _ -> (assignment::concrete,symbolic)
      | _ -> failwith ("unsupported assignment in split_assignments: " ^
                       (render_tterm assignment.lhs) ^
                       " = " ^ (render_tterm assignment.rhs)))

let apply_assignments assignments terms =
  List.fold assignments ~init:terms ~f:(fun terms {lhs;rhs} ->
      List.map terms ~f:(replace_tterm lhs rhs))

let render_assumptions assumptions  =
  String.concat ~sep:"\n" (List.map assumptions ~f:(fun t ->
      "//@ assume(" ^
      (match t.v with
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
  String.concat ~sep:"\n" (List.map assignments ~f:(fun {lhs;rhs} -> render_eq_sttmt ~is_assert:false lhs rhs))

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

let bubble_equalities tterms =
  List.sort tterms ~compare:(fun t1 t2 ->
      match (t1.v,t2.v) with
      | (Bop (Eq,_,_), Bop (Eq,_,_)) -> 0
      | (Bop (Eq,_,_), _) -> -1
      | (_, Bop(Eq,_,_)) -> 1
      | (_,_) -> 0)

let is_there_device_constraint constraints =
  List.exists constraints ~f:(fun tterm ->
      match tterm.v with
      | Bop (Eq, lhs, {v=Id x; t}) when String.equal x "device_0" ->
        true
      | _ -> false)

let guess_support_assignments constraints symbs =
  (*printf "guess constraints\n";
  List.iter constraints ~f:(fun xxx -> printf "%s\n" (render_tterm xxx));
  printf "symbols:\n";
  Set.iter symbs ~f:(fun name -> printf "%s\n" name;);*)
  let there_is_a_device_constraint = is_there_device_constraint constraints in
  let (assignments,_) =
    List.fold (bubble_equalities constraints) ~init:([],symbs) ~f:(fun (assignments,symbs) tterm ->
        (* printf "considering %s\n" (render_tterm tterm); *)
        match tterm.v with
        | Bop (Eq, {v=Id x;t}, rhs) when String.Set.mem symbs x ->
          (*printf "match 1st %s: %s\n" x (ttype_to_str t);*)
          ({lhs={v=Id x;t};rhs}::assignments, String.Set.remove symbs x)
        | Bop (Eq, lhs, {v=Id x;t}) when String.Set.mem symbs x ->
          (*printf "match 2nd %s: %s\n" x (ttype_to_str t);*)
          ({lhs={v=Id x;t};rhs=lhs}::assignments, String.Set.remove symbs x)
        | Bop (Le, {v=Int i;t=lt}, {v=Id x;t}) when String.Set.mem symbs x ->
          (* Stupid hack. If the variable is constrained to not be equal to another variable, we assume they have the same lower bound and assign the second one to bound+2 *)
          if List.exists constraints (fun cstr -> match cstr with {v=Bop (Eq,{v=Bool false;_},{v=Bop (Eq,{v=Id _;_},{v=Id r;_});_});_} when r = x -> true | _ -> false) then
              ({lhs={v=Id x;t};rhs={v=Int (i+2);t=lt}}::assignments, String.Set.remove symbs x)
          else if there_is_a_device_constraint then (*Dirty hack for a difficult case, analyzed by hand*)
              ({lhs={v=Id x;t};rhs={v=Int 1;t=lt}}::assignments, String.Set.remove symbs x)
          else
              ({lhs={v=Id x;t};rhs={v=Int i;t=lt}}::assignments, String.Set.remove symbs x)
        | Bop (Le, {v=Id x;t}, rhs) when String.Set.mem symbs x ->
          ({lhs={v=Id x;t};rhs}::assignments, String.Set.remove symbs x)
        | _ -> (assignments, symbs))
  in
  assignments

let ids_from_varspecs_map vars =
  List.fold (Map.data vars) ~init:String.Set.empty ~f:(fun acc var ->
      String.Set.add acc var.name)

let simplify_assignments assignments =
  List.fold assignments ~init:assignments ~f:(fun acc assignment ->
      List.map acc ~f:(fun {lhs;rhs} ->
          {lhs;rhs = replace_tterm assignment.lhs assignment.rhs rhs}))

let fix_mistyped_tip_ret tterm =
  match tterm.v with
  | Id name when String.equal name "tip_ret"
    -> {v=Not {v=Bop (Eq,{v=Int 0;t=Sint32},tterm);
               t=Boolean};
        t=Boolean}
  | Bop (Bit_and, _, _) -> {v=Not {v=Bop (Eq,{v=Int 0;t=Sint32},tterm);t=Boolean};t=Boolean}
  | _ -> tterm


let render_output_check
    ret_val ret_name ret_type model_constraints
    hist_symbs args_post_conditions cmplxs
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
  let cmplx_symbs = ids_from_varspecs_map cmplxs in
  let unalloc_symbs =
    String.Set.diff
      (String.Set.diff
         (String.Set.diff
            (ids_from_terms output_constraints)
            output_symbs)
         hist_symbs)
      cmplx_symbs
  in
  let support_assignments =
    guess_support_assignments output_constraints unalloc_symbs
  in
  let assignments = assignments@support_assignments in
  let (concrete_assignments,
       symbolic_var_assignments) = split_assignments assignments
  in
  let symbolic_var_assignments =
    simplify_assignments symbolic_var_assignments
  in
  (* printf "substitution schema:\n"; *)
  (* List.iter symbolic_var_assignments ~f:(fun {lhs;rhs} -> *)
  (*     printf "%s = %s\n" (render_tterm lhs) (render_tterm rhs)); *)
  let upd_model_constraints =
    apply_assignments symbolic_var_assignments output_constraints
  in
  "// Output check\n" ^
  "// Input assumptions\n" ^
  (render_input_assumptions input_constraints) ^ "\n" ^
  "// Support assignments of unbound symbols\n" ^
  (* VV For the "if (...)" condition, which involves
     VV the original value (non-renamed)*)
  (render_some_assignments_as_assumptions symbolic_var_assignments) ^ "\n" ^
  "// Concrete equalities: \n" ^
  (render_concrete_assignments_as_assertions concrete_assignments) ^ "\n" ^
  "// Model constraints: \n" ^
  (String.concat ~sep:"\n"
     (List.map upd_model_constraints ~f:(fun constr -> match (fix_mistyped_tip_ret constr) with
                                                       | {v=Bop (Eq, lhs, rhs);t=_} -> render_eq_sttmt ~is_assert:true lhs rhs
                                                       | c -> "/*@ assert(" ^ (render_tterm c) ^ "); @*/")))

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

let rec build_decision_tree results =
  let handle_two_constraints hd1 hd2 =
    let results = hd1::hd2::[] in
    match find_complementary_sttmts hd1.post_statements hd2.post_statements with
    | None ->
      failwith ("No complementary statements found.")
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
      Alternative_by_constraint ((sttmt1, build_decision_tree results_pro1),(sttmt2, build_decision_tree results_pro2))
  in
  match results with
  | [] -> failwith "There must be at least one tip-call result"
  | hd :: [] -> Single_result hd
  | hd1 :: hd2 :: [] ->
    if term_eq hd1.ret_val.v hd2.ret_val.v then
      handle_two_constraints hd1 hd2
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
  | _ ->
    assert (4 = List.length results); (* This is special-cased. *)
    assert (List.for_all results ~f:(fun res -> term_eq res.ret_val.v (List.nth_exn results 0).ret_val.v)); (* No alternative by ret *)
    (* All results have 2 statements except one *)
    let single_statement_result = List.find_exn results ~f:(fun rs -> List.length rs.post_statements = 1) in
    (* Add a statement to make the rest easier - it is implied by the existing statement, anyway *)
    let results = List.map results ~f:(fun rs -> 
      if rs = single_statement_result then
        match rs.post_statements with
          (* 0 != (x & N) for any N implies 0 != x *)
        | {v=Bop (Bit_and, {v=Id var_v;t=var_t}, {v=_;t=_});t=_} :: [] ->
            let new_post = {v=Id var_v;t=var_t} in
            {args_post_conditions=rs.args_post_conditions;
             ret_val=rs.ret_val;
             post_statements=new_post::rs.post_statements}
        | _ -> failwith "Sorry, you're on your own, welcome to special-case world!"
      else rs)
    in
    assert (List.for_all results ~f:(fun res -> List.length res.post_statements = 2));
    (* From the given 'results', find the element that has a matching post-statement with 'result' *)
    (* Return (the matching element, the matching statement, the other elements) *)
    let rec find_matching_result res results =
      match results with
      | hd :: tl ->
          begin
          match List.find res.post_statements ~f:(fun st ->
                  List.exists hd.post_statements ~f:(fun st2 -> term_eq st2.v st.v)) with
          | Some st -> (hd, st, tl)
          | None ->
              let (mate, mats, rest) = find_matching_result res tl in
              (mate, mats, hd :: rest)
          end
      | [] -> failwith "Can't find a matching result!"
    in
    let remove_statement res stmt =
      {args_post_conditions=res.args_post_conditions;
       ret_val=res.ret_val;
       post_statements=List.filter res.post_statements ~f:(fun st -> not(term_eq st.v stmt.v))}
    in
    match results with
    | hd1 :: tl1 ->
        begin
        let (mat1, st1, rest) = find_matching_result hd1 tl1 in
        assert (2 = List.length rest);
        match rest with
        | hd2 :: tl2 ->
            let (mat2, st2, rest) = find_matching_result hd2 tl2 in
            assert (0 = List.length rest);
            (* Now that we have cleanly grouped our 4 statements into 2, we make a proper 2-level decision tree *)
            Alternative_by_constraint ((st1,
                                        (handle_two_constraints (remove_statement hd1 st1) (remove_statement mat1 st1))),
                                       (st2,
                                        (handle_two_constraints (remove_statement hd2 st2) (remove_statement mat2 st2))))
        | _ -> failwith "should not happen"
        end
    | _ -> failwith "should not happen, bis"

let rec render_post_assertions dtree ret_name ret_type hist_symbs cmplxs =
  match dtree with
  | Single_result res ->
   (render_args_post_conditions ~is_assert:false res.args_post_conditions) ^ "\n" ^
   (render_output_check
       res.ret_val ret_name ret_type
       res.post_statements hist_symbs
       res.args_post_conditions cmplxs) ^ "\n"
  | Alternative_by_constraint ((sttmt1,dtree1),(sttmt2,dtree2)) ->
    "if (" ^ (render_tterm sttmt1) ^ ") {\n" ^
      (render_post_assertions dtree1 ret_name ret_type hist_symbs cmplxs) ^
    "} else {\n" ^
      (render_post_assertions dtree2 ret_name ret_type hist_symbs cmplxs) ^
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
    (render_post_assertions dtree1 ret_name ret_type hist_symbs cmplxs) ^
    "} else {\n " ^
    (render_post_assertions dtree2 ret_name ret_type hist_symbs cmplxs) ^
    "}"

let render_export_point name =
  "int " ^ name ^ ";\n"

let render_assignments args =
  String.concat ~sep:"\n"
    (List.join
       (List.map args ~f:(fun arg ->
            List.map (if arg.value.v = Undef then []
                      else
                        gen_plain_equalities {lhs={v=Id arg.name;t=arg.value.t;};
                                              rhs=arg.value})
              ~f:render_assignment)))

let render_equality_assumptions args =
  String.concat ~sep:"\n"
    (List.map (String.Map.data args) ~f:(fun arg ->
         match arg.value.v with
         | Undef -> ""
         | _ -> "//@ assume(" ^ arg.name ^ " == "
                ^ (render_tterm arg.value) ^ ");"))

let render_tip_fun_call
    {context;results}
    export_point free_vars hist_symbols
    ~render_assertions
    cmplxs =
  (render_extra_pre_conditions context) ^ "\n" ^
  (render_fcall_with_prelemmas context) ^
  (render_postlemmas context) ^
  (* "// The legibility of these assignments is ensured by analysis.ml\n" ^ *)
  (* (render_equality_assumptions free_vars) ^ "\n" ^ *)
  (render_export_point export_point) ^
  (if render_assertions then
     let dtree = build_decision_tree
         (List.sort ~compare:(fun res1 res2 ->
              (List.length res1.post_statements) -
              (List.length res2.post_statements))
         results) in
     render_post_assertions
       dtree context.ret_name context.ret_type hist_symbols cmplxs
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
  String.concat ~sep:"\n" (List.map (List.sort ~compare:(fun a b ->
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

let render_args_hack args =
  (* Render declarations first, VeriFast complains otherwise *)
  String.concat ~sep:"\n"
    (List.map (List.filter args ~f:(fun spec -> is_pointer_t spec.value.t))
       ~f:(fun spec -> (ttype_to_str spec.value.t) ^ " " ^
                       (spec.name) ^ "bis;")) ^ "\n" ^
  (* Then the assignments *)
  String.concat ~sep:"\n"
    (List.map (List.filter args ~f:(fun spec -> is_pointer_t spec.value.t))
       ~f:(fun spec -> (spec.name) ^ " = " ^ (spec.name) ^ "bis;\n" ^
                       "*(&(" ^ (spec.name) ^ ")) = " ^ (spec.name) ^ "bis;")) ^ "\n" ^
  (* Then the assumptions, which would be overwritten by assignments otherwise *)
  String.concat ~sep:"\n"
    (List.map (List.filter args ~f:(fun spec -> is_pointer_t spec.value.t))
       ~f:(fun spec -> "//@ assume(" ^ (spec.name) ^ " == " ^ (spec.name) ^ "bis);")) ^ "\n"

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

let discard_redundant_preconditions ir =
  let filter_redundant_preconditions prev_postconds preconds =
    List.filter preconds ~f:(fun precond ->
        not (List.exists prev_postconds
               ~f:(fun postcond ->
                   Ir.term_eq precond.lhs.v postcond.lhs.v &&
                   Ir.term_eq precond.rhs.v postcond.rhs.v)))
  in
  let (last_postconds, hist_calls) =
    List.fold_map ir.hist_calls ~init:[] ~f:(fun last_postconds hist_call ->
        (gen_plain_equalities_for_all hist_call.result.args_post_conditions,
         {context = {hist_call.context with
                     extra_pre_conditions =
                       filter_redundant_preconditions
                         last_postconds
                         (gen_plain_equalities_for_all
                            hist_call.context.extra_pre_conditions)};
          result = hist_call.result}))
  in
  let tip_call = {context = {ir.tip_call.context with
                             extra_pre_conditions =
                               filter_redundant_preconditions
                                 last_postconds
                                 (gen_plain_equalities_for_all
                                    ir.tip_call.context.extra_pre_conditions)};
                  results = ir.tip_call.results}
  in
  {ir with hist_calls; tip_call}

let render_ir ir fout ~render_assertions =
  let ir = discard_redundant_preconditions ir in
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
      Out_channel.output_string cout (render_args_hack ir.arguments);
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
                                        ~render_assertions
                                        ir.cmplxs);
      Out_channel.output_string cout (render_final ir.finishing
                                        ~catch_leaks:render_assertions);
      Out_channel.output_string cout "}\n")
