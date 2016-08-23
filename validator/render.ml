open Core.Std
open Ir

let rec render_eq_sttmt ~is_assert out_arg (out_val:tterm) =
  let head = (if is_assert then "assert" else "assume") in
  match out_val.v with
  | Struct (_, fields) ->
    (*TODO: check that the types of Str (_,fts)
      are the same as in fields*)
    String.concat (List.map fields ~f:(fun {name;value} ->
      render_eq_sttmt ~is_assert (out_arg ^ "." ^ name) value))
  | _ -> "//@ " ^ head ^ "(" ^ out_arg ^ " == " ^
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
                              ~f:(fun {name;value} ->
                                  render_eq_sttmt ~is_assert
                                    name value)))

let render_post_assumptions post_statements =
  (String.concat ~sep:"\n" (List.map post_statements
                              ~f:(fun t ->
                                  "/*@ assume(" ^
                                  (render_tterm t) ^
                                  ");@*/")))

let render_tip_post_sttmts {args_post_conditions;
                            ret_val=_;post_statements} =
  (render_post_assumptions post_statements) ^ "\n" ^
  (render_args_post_conditions ~is_assert:true args_post_conditions)

let render_ret_equ_sttmt ~is_assert ret_name ret_val =
  match ret_name with
  | Some name -> (render_eq_sttmt ~is_assert name ret_val) ^ "\n"
  | None -> "\n"

let render_hist_fun_call {context;result} =
  (render_fcall_with_lemmas context) ^
  (render_args_post_conditions ~is_assert:false result.args_post_conditions) ^
  match result.ret_val.t with
  | Ptr _ -> "/* Do not render the return ptee assumption for hist calls */\n"
  | _ -> render_ret_equ_sttmt ~is_assert:false context.ret_name result.ret_val

let find_false_eq_sttmts (sttmts:tterm list) =
  List.filter sttmts ~f:(fun sttmt ->
      match sttmt.v with
      | Bop (Eq,{v=Bool false;t=Boolean},_) -> true
      | _ -> false)

let find_complementary_sttmts sttmts1 sttmts2 =
  let find_from_left sttmts1 (sttmts2:tterm list) =
    List.find_map (find_false_eq_sttmts sttmts1) ~f:(fun sttmt1 ->
        match sttmt1.v with
        | Bop (_,_,rhs) ->
          List.find sttmts2 ~f:(fun sttmt2 -> term_eq rhs.v sttmt2.v)
        | _ -> None)
  in
  match find_from_left sttmts1 sttmts2 with
  | Some st -> Some (st,false)
  | None -> Option.map (find_from_left sttmts2 sttmts1)
              ~f:(fun rez -> (rez,true))

let render_2tip_post_assertions res1 res2 ret_name =
  if term_eq res1.ret_val.v res2.ret_val.v then
    begin
      match find_complementary_sttmts
              res1.post_statements
              res2.post_statements with
      | Some (sttmt,fst) ->
        begin
          let res1_assertions =
            (render_tip_post_sttmts res1 ^ "\n" ^
             render_ret_equ_sttmt ~is_assert:true ret_name res1.ret_val)
          in
          let res2_assertions =
            (render_tip_post_sttmts res2 ^ "\n" ^
             render_ret_equ_sttmt ~is_assert:true ret_name res2.ret_val)
          in
          let (pos_sttmts,neg_sttmts) =
            if fst then
              res1_assertions,res2_assertions
            else
              res2_assertions,res1_assertions
          in
          "if (" ^ (render_tterm sttmt) ^ ") {\n" ^
          pos_sttmts ^ "\n} else {\n" ^
          neg_sttmts ^ "}\n"
        end
      | None -> failwith "Tip calls non-differentiated by ret, nor \
                          by a complementary post-conditions are \
                          not supported"
    end
  else
    let rname = match ret_name with
      | Some n -> n
      | None -> failwith "this can't be true!"
    in
    "if (" ^ rname ^ " == " ^ (render_tterm res1.ret_val) ^ ") {\n" ^
    (render_tip_post_sttmts res1) ^ "\n} else {\n" ^
    (render_tip_post_sttmts res2) ^ "\n" ^
    (render_ret_equ_sttmt ~is_assert:true ret_name res2.ret_val) ^ "}\n"

let render_export_point name =
  "int " ^ name ^ ";\n"

let rec render_assignment var =
  match var.value.v with
  | Struct (_, fvals) ->
    (*TODO: make sure that the var_value.t is also Str .*)
    String.concat ~sep:"\n"
      (List.map fvals
         ~f:(fun {name;value} ->
             render_assignment {name=(var.name ^ "." ^ name);value} ^ ";"))
  | Undef -> ""
  | _ -> var.name ^ " = " ^ (render_tterm var.value)

let render_assignments args =
  String.concat ~sep:"\n"
    (List.map args ~f:(fun arg ->
       render_assignment arg ^ ";"))

let render_equality_assumptions args =
  String.concat ~sep:"\n"
    (List.map (String.Map.data args) ~f:(fun arg ->
         match arg.value.v with
         | Undef -> ""
         | _ -> "//@ assume(" ^ arg.name ^ " == "
                ^ (render_tterm arg.value) ^ ");"))

let render_tip_fun_call {context;results} export_point free_vars =
  (render_fcall_with_lemmas context) ^
  "// The legibility of these assignments is ensured by analysis.ml\n" ^
  (render_equality_assumptions free_vars) ^ "\n" ^
  (render_export_point export_point) ^
  (match results with
   | result :: [] ->
     (render_tip_post_sttmts result) ^ "\n" ^
     (render_ret_equ_sttmt ~is_assert:true context.ret_name result.ret_val)
   | res1 :: res2 :: [] ->
     render_2tip_post_assertions res1 res2 context.ret_name
   | [] -> failwith "There must be at least one tip call."
   | _ -> failwith "More than two outcomes are not supported.") ^ "\n"


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
  String.concat ~sep:"\n" (List.map assumptions ~f:(fun t ->
    "//@ assume(" ^ (render_tterm t) ^ ");")) ^ "\n"

let render_allocated_args args =
  String.concat ~sep:"\n"
    (List.map args
       ~f:(fun spec -> (ttype_to_str spec.value.t) ^ " " ^
                       (spec.name) ^ ";")) ^ "\n"

let render_final finishing =
  if finishing then
    "/* This sequence must terminate correctly: no need for assume(false);"
  else
    "//@ assume(false);\n"

let render_ir ir fout =
  Out_channel.with_file fout ~f:(fun cout ->
      Out_channel.output_string cout ir.preamble;
      Out_channel.output_string cout (render_cmplexes ir.cmplxs);
      Out_channel.output_string cout (render_vars_declarations
                                        (String.Map.data ir.free_vars));
      Out_channel.output_string cout (render_allocated_args ir.arguments);
      Out_channel.output_string cout (render_context_assumptions
                                        ir.context_assumptions);
      Out_channel.output_string cout (render_tmps ir.tmps);
      Out_channel.output_string cout (render_assignments ir.arguments);
      Out_channel.output_string cout (render_hist_calls ir.hist_calls);
      Out_channel.output_string cout (render_tip_fun_call
                                        ir.tip_call ir.export_point
                                        ir.free_vars);
      Out_channel.output_string cout (render_final ir.finishing);
      Out_channel.output_string cout "}\n")
