open Core.Std
open Parser_util
open Assumption

let rec replace_in_term old_t new_t term =
  if term_eq term old_t then new_t else
    match term with
    | Not t -> Not (replace_in_term old_t new_t t)
    | Cmp (cmp,lhs,rhs) -> Cmp (cmp,replace_in_term old_t new_t lhs,
                                replace_in_term old_t new_t rhs)
    | _ -> term

let replace_in_list id_old id_new ass_list =
  List.map ass_list ~f:(replace_in_term id_old id_new)

let choose_simpler t1 t2 =
  match t1 with
  | Int _ | Bool _ -> (t1,t2)
  | Id i1 -> begin
      match t2 with
      | Int _ | Bool _ -> (t2,t1)
      | Id i2 -> if (String.length i1) < (String.length i2) then (t1,t2) else (t2,t1)
      | _ -> (t1,t2)
    end
  | Cmp _ | Not _ -> (t2,t1)

let extract_equalities ass_list =
  List.partition_tf ass_list ~f:(function Cmp(Eq,_,_) -> true | _ -> false)

let replace_with_equalities ass_list eqs =
  List.fold eqs ~init:ass_list
    ~f:(fun acc eq ->
         match eq with
         | Cmp(Eq,lhs,rhs) ->
           let (old_t,new_t) = choose_simpler lhs rhs in
           replace_in_list old_t new_t acc
         | _ -> failwith "eqs must contain only equalities")

let print_assumption_list al =
  List.iter al ~f:(fun ass ->
      printf "%s\n" (Assumption.term_to_string ass))


let simplify ass_list =
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
  let ass_list = replace_with_equalities non_eq_assumptions eqs in
  remove_trues ass_list

let () =
  let ass_list = parse_file Sys.argv.(1) in
  let ass_list = simplify ass_list in
  print_assumption_list ass_list
