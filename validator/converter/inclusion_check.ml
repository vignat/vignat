open Core.Std
open Parser_util
open Assumption

let rec replace_in_term old_t new_t term =
  if term_eq term old_t then new_t else
    match term with
    | Not t -> Not (replace_in_term old_t new_t t)
    | Cmp (cmp,lhs,rhs) -> Cmp (cmp,replace_in_term old_t new_t lhs,
                                replace_in_term old_t new_t rhs)
    | Call (fname,args) -> Call (fname,replace_in_list old_t new_t args)
    | _ -> term
and replace_in_list id_old id_new term_list =
  List.map term_list ~f:(replace_in_term id_old id_new)

let rec term_contains sub_t t =
  if term_eq t sub_t then true
  else match t with
    | Int _ | Bool _ | Id _ -> false
    | Call (_, args) -> List.exists args ~f:(term_contains sub_t)
    | Cmp (_,lhs,rhs) -> (term_contains sub_t lhs) || (term_contains sub_t rhs)
    | Not t -> term_contains sub_t t

let rec term_depth = function
  | Int _ | Id _ | Bool _ -> 0
  | Cmp (_,lhs,rhs) -> (max (term_depth lhs) (term_depth rhs)) + 1
  | Call (_,args) -> (List.reduce_exn
                        (List.map args ~f:term_depth)
                        ~f:Int.max) + 1
  | Not t -> 1 + (term_depth t)

let choose_simpler t1 t2 keep_that =
  if term_contains keep_that t1 then (t1,t2) else
  if term_contains keep_that t2 then (t2,t1) else
    match t1 with
    | Int _ | Bool _ -> (t1,t2)
    | Id _ -> begin
        match t2 with
        | Int _ | Bool _ -> (t2,t1)
        | _ -> (t1,t2)
      end
    | _ -> if (term_depth t1) < (term_depth t2) then (t1,t2) else (t2,t1)

let extract_equalities ass_list =
  List.partition_tf ass_list ~f:(function Cmp(Eq,_,_) -> true | _ -> false)

let remove_trivial_eqs eqs =
  List.filter eqs ~f:(function Cmp(Eq,lhs,rhs) -> not (term_eq lhs rhs) | _ -> true)

(* The equalities that do not reduce to a simple variable renaming:
   anything except (a = b).*)
let get_meaningful_equalities eqs =
  List.filter eqs ~f:(function Cmp (Eq,lhs,rhs) ->
      begin
        match lhs,rhs with
        | Id _, Id _ -> false
        | _, _ -> true
      end
                             | _ -> failwith "only equalities here")

let replace_with_equalities ass_list eqs keep_that =
  List.fold eqs ~init:ass_list
    ~f:(fun acc eq ->
         match eq with
         | Cmp(Eq,lhs,rhs) ->
           let (new_t,old_t) = choose_simpler lhs rhs keep_that in
           replace_in_list old_t new_t acc
         | _ -> failwith "eqs must contain only equalities")

let print_assumption_list al =
  List.iter al ~f:(fun ass ->
      printf "%s\n\n" (Assumption.term_to_string ass))

let rec get_ids_from_term = function
  | Int _ | Bool _ -> []
  | Id x -> [x]
  | Cmp (_,lhs,rhs) ->
    List.dedup ~compare:String.compare (get_ids_from_term lhs)@(get_ids_from_term rhs)
  | Call (_, args) ->
    List.dedup ~compare:String.compare
      (List.join (List.map args ~f:get_ids_from_term))
  | Not t -> get_ids_from_term t

let index_assumptions ass_list =
  List.fold ass_list ~init:String.Map.empty ~f:(fun acc ass ->
      let ids = get_ids_from_term ass in
      List.fold ids ~init:acc ~f:(fun acc id ->
          String.Map.add acc ~key:id
            ~data:(match String.Map.find acc id with
                | Some ass_list -> ass::ass_list
                | None -> [ass])))

let take_relevant ass_list interesting_id =
  let map = index_assumptions ass_list in
  if not (String.Map.mem map interesting_id) then
    failwith (interesting_id ^ " is never mentioned in this assumption list")
  else
    let retreive_relevant_terms id =
      match String.Map.find map id with
      | Some l -> l
      | None -> failwith "inconsistent indexing"
    in
    let rec take_relevant id processed =
      if String.Set.mem processed id then ([],processed)
      else
        let processed = String.Set.add processed id in
        let rele_terms = retreive_relevant_terms id in
        let rele_ids =
          List.dedup ~compare:String.compare
            (List.join (List.map rele_terms ~f:get_ids_from_term))
        in
        let (deep_terms, procd) =
          List.fold rele_ids ~init:([],processed)
            ~f:(fun (acc,procd) id ->
                let (terms,procd) = take_relevant id procd in
                (terms@acc,procd))
        in
        (rele_terms@deep_terms, procd)
    in
    let (terms,_) = take_relevant interesting_id String.Set.empty in
    List.dedup terms

let simplify ass_list keep_that =
  let rec remove_double_negation a =
    match a with
    | Not (Not t) -> remove_double_negation t
    | Cmp (cmp,lhs,rhs) -> Cmp (cmp, remove_double_negation lhs,
                                remove_double_negation rhs)
    | _ -> a
  in
  let remove_trues al =
    List.filter al ~f:(function Bool true -> false | _ -> true)
  in
  let ass_list = List.map ass_list ~f:remove_double_negation in
  let (eqs,non_eq_assumptions) = (extract_equalities ass_list) in
  let eqs = remove_trivial_eqs eqs in
  let ass_list = non_eq_assumptions in
  let ass_list = replace_with_equalities ass_list eqs keep_that in
  let ass_list = (get_meaningful_equalities eqs) @ ass_list in
  remove_trues ass_list

let () =
  let interesting = Sys.argv.(2) in
  let interesting_id = Id interesting in
  let ass_list = parse_file Sys.argv.(1) in
  let ass_list = simplify ass_list interesting_id in
  print_assumption_list (take_relevant ass_list interesting)
