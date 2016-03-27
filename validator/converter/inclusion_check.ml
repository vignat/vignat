open Core.Std
open Parser_util
open Ir

let rec term_depth = function
  | Bop (_,lhs,rhs) ->
    1 + max (term_depth lhs.v) (term_depth rhs.v)
  | Apply (_,args) ->
    1 + List.fold args ~init:0
      ~f:(fun acc arg -> max acc (term_depth arg.v))
  | Id _ -> 1
  | Struct (_,fields) ->
    List.fold fields ~init:0 ~f:(fun acc field ->
        max acc (term_depth field.value.v))
  | Int _ -> 0
  | Bool _ -> 0
  | Not t -> 1 + term_depth t.v
  | Str_idx (term,_) ->
    1 + term_depth term.v
  | Deref term -> 1 + term_depth term.v
  | Fptr _ -> 0
  | Addr tterm -> 1 + term_depth tterm.v
  | Cast (_,tterm) ->
    1 + term_depth tterm.v
  | Undef -> 0

let choose_simpler t1 t2 keep_these =
  let contain_any term =
    List.exists keep_these ~f:(fun k -> term_contains_term t1 k)
  in
  match contain_any t1, contain_any t2 with
  | true, true -> None
  | true, false -> Some (t1,t2)
  | false, true -> Some (t2,t1)
  | false, false ->
    if (term_depth t1) < (term_depth t2)
    then Some (t1,t2)
    else Some (t2,t1)

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

let replace_with_equalities ass_list eqs keep_these =
  List.fold eqs ~init:ass_list
    ~f:(fun acc eq ->
         match eq.v with
         | Bop(Eq,lhs,rhs) ->
           begin
             match choose_simpler lhs.v rhs.v keep_these with
             | Some (new_t,old_t) ->
               replace_term_in_tterms old_t new_t acc
             | None -> acc
           end
         | _ -> failwith "eqs must contain only equalities")

let print_assumption_list al =
  List.iter al ~f:(fun ass ->
      printf "%s\n\n" (render_term ass.v))

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
      List.fold ids ~init:acc ~f:(fun acc id ->
          String.Map.add acc ~key:id
            ~data:(match String.Map.find acc id with
                | Some ass_list -> ass::ass_list
                | None -> [ass])))

let take_relevant (ass_list:tterm list) interesting_ids =
  let map = index_assumptions ass_list in
  if not (List.exists interesting_ids ~f:(String.Map.mem map)) then
    failwith ((String.concat interesting_ids) ^ " is never mentioned in this assumption list")
  else
    let retreive_relevant_terms id =
      match String.Map.find map id with
      | Some l -> l
      | None -> []
    in
    let rec take_relevant id processed =
      if String.Set.mem processed id then ([],processed)
      else
        let processed = String.Set.add processed id in
        let rele_terms = retreive_relevant_terms id in
        let rele_ids =
          List.dedup ~compare:String.compare
            (List.join (List.map rele_terms ~f:get_ids_from_tterm))
        in
        let (deep_terms, procd) =
          List.fold rele_ids ~init:([],processed)
            ~f:(fun (acc,procd) id ->
                let (terms,procd) = take_relevant id procd in
                (terms@acc,procd))
        in
        (rele_terms@deep_terms, procd)
    in
    let take_relevant_list ids =
      fst (List.fold ids ~init:([],String.Set.empty) ~f:(fun (terms,procd) id ->
          let (id_terms,procd) = take_relevant id procd in
          (id_terms @ terms,procd)))
    in
    List.dedup (take_relevant_list interesting_ids)

let simplify ass_list keep_these =
  let remove_double_negation a =
    a |> call_recursively_on_tterm (fun term ->
        match term with
        | Not {v=Not tt;t=_} -> Some tt.v
        | _ -> None)
  in
  let remove_trues al =
    List.filter al ~f:(function {v=Bool true;t=_} -> false | _ -> true)
  in
  let ass_list = List.map ass_list ~f:remove_double_negation in
  let (eqs,non_eq_assumptions) = (extract_equalities ass_list) in
  let eqs = remove_trivial_eqs eqs in
  let ass_list = non_eq_assumptions in
  let ass_list = replace_with_equalities ass_list eqs keep_these in
  let ass_list = (get_meaningful_equalities eqs) @ ass_list in
  remove_trues ass_list

let load_n_simplify_assumptions fname importants =
  let important_ids = List.map importants ~f:(fun x -> Id x) in
  let assumptions = parse_file fname in
  let assumptions = simplify assumptions important_ids in
  take_relevant assumptions importants

let get_all_ids assumptions =
  (List.map assumptions ~f:get_ids_from_tterm) |>
  List.join |>
  String.Set.of_list

let find_congruent_assumption target heap =
  match target with (*TODO: differentiate known/unknown ids*)
  | Bop (op,{v=Id lhs;t=_},{v=Id rhs;t=_}) ->
    List.find_map heap ~f:(function
        | {v=Bop (aop,{v=Id alhs;t=t1},{v=Id arhs;t=t2});t=_}
          when op = aop ->
          Some [{v=(Bop (Eq,{v=Id lhs;t=t1},{v=Id alhs;t=t1}));t=Boolean};
                {v=(Bop (Eq,{v=Id rhs;t=t2},{v=Id arhs;t=t2}));t=Boolean}]
        | _ -> None)
  | _ -> None

type assignment = (string*term)

let is_congruent given test : assignment list option =
  let given_ids = get_all_ids given in
  let unbound_ids =
    String.Set.diff (String.Set.of_list (get_ids_from_tterm test))
      given_ids
  in
  match test with
  | {v=Bop (Eq,{v=Id lhs;t=_},{v=Id rhs;t=_})} ->
    let lhs_unbound = String.Set.mem unbound_ids lhs in
    let rhs_unbound = String.Set.mem unbound_ids rhs in
    begin
      match lhs_unbound,rhs_unbound with
      | true,true -> Some [lhs,Id rhs]
      | true,false -> Some [lhs,Id rhs]
      | false,true -> Some [rhs,Id lhs]
      | false,false -> if String.equal lhs rhs then Some []
        else if tterms_contain_term given test.v then Some []
        else None
    end
  | {v=Bop (op,{v=Id lhs;t=_},{v=Id rhs;t=_});t=_} ->
    List.find_map given ~f:(function
        | {v=Bop (aop,{v=Id alhs;t=_},{v=Id arhs;t=_});t=_}
          when op = aop ->
          let lhs_unbound = String.Set.mem unbound_ids lhs in
          let rhs_unbound = String.Set.mem unbound_ids rhs in
          begin
            match lhs_unbound,rhs_unbound with
            | true,true -> Some [lhs,Id alhs;rhs,Id arhs]
            | true,false ->
              if String.equal rhs arhs then
                Some [lhs,Id alhs]
              else
                None
            | false,true ->
              if String.equal lhs alhs then
                Some [rhs,Id arhs]
              else
                None
            | false,false -> if String.equal lhs alhs && String.equal rhs arhs then
                Some []
              else
                None
          end
        | _ -> None)
  | _ -> None

let can_be_congruent given test_set =
  let rec impl given test_set : assignment list option =
    let (next_test,rest) =
      let given_ids = get_all_ids given in
      match List.partition_tf test_set ~f:(fun ass ->
          List.exists (get_ids_from_tterm ass) ~f:(String.Set.mem given_ids))
      with
      | (ass::tl,rest) -> (ass,tl@rest)
      | ([],hd::tl) -> (hd,tl)
      | ([],[]) -> ({v=Bool true;t=Boolean},[])
    in
    printf "testing %s \n" (render_tterm next_test);
    match next_test with
    | {v=Bool true;t=_} -> Some []
    | _ ->
      match is_congruent given next_test with
      | Some assignments ->
        let test_left =
          List.map rest ~f:(fun assumption ->
              List.fold assignments ~init:assumption ~f:(fun acc (name,term) ->
                  replace_term_in_tterm (Id name) term acc))
        in
        begin
          match impl (next_test::given) test_left with
          | Some assigns -> Some (assigns@assignments)
          | None -> None
        end
      | None -> None
  in
  impl given test_set

let () =
  let task = Ir.task_of_sexp (Sexp.load_sexp "./tasks.sexp") in
  let _ =
    Sys.command ( "~/proj/verifast-1757/bin/verifast -c -I ../../nat " ^
                  " -breakpoint " ^ (string_of_int task.assert_lino) ^
                  " -breakpoint_context_file bcf.txt " ^
                  task.filename )
  in
  let interesting = List.join (List.map task.exists_such
                                 ~f:get_ids_from_tterm) in
  let target_assumptions =
    load_n_simplify_assumptions "bcf.txt" interesting in
  print_assumption_list task.path_constraints;
  print_assumption_list task.exists_such;
  print_assumption_list target_assumptions;
  match can_be_congruent target_assumptions task.exists_such with
  | Some assignments ->
    printf "congruent: \n";
    List.iter assignments ~f:(fun (var,value) ->
        printf "%s := %s\n" var (render_term value))
  | None -> printf "Not congruent\n"
