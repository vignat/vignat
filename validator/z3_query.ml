open Core
open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector

let output_queries = true

let show_vars vars =
  if output_queries then begin
    Printf.printf ";vars:\n";
    List.iter (Map.data vars) ~f:(fun v ->
        Printf.printf "(declare-fun %s () Int)\n" (Expr.to_string v))
  end

let show_funs funs =
  if output_queries then begin
    Printf.printf ";funs:\n";
    List.iter (Map.data funs) ~f:(fun (f,_) ->
        Printf.printf "%s\n" (FuncDecl.to_string f));
  end

let show_assumptions assumptions =
  if output_queries then begin
    Printf.printf "\n\n;assumptions:\n";
    List.iter assumptions ~f:(fun ass ->
        Printf.printf "(assert %s)\n" (Expr.to_string ass));
  end

let show_assignment assgn =
  if output_queries then begin
    Printf.printf ";assignment:\n (assert %s)\n" (Expr.to_string assgn);
  end

let show_negation neg =
  if output_queries then begin
    Printf.printf ";assertion negation: :\n (assert %s)\n" (Expr.to_string neg);
  end

let show_theorem theorem =
  if output_queries then begin
    Printf.printf ";theorem:\n (assert %s)\n" (Expr.to_string theorem);
  end

let show_result result solver =
  if output_queries then begin
    match result with
    | SATISFIABLE -> Printf.printf "sat\n"
    | UNSATISFIABLE -> Printf.printf "unsat\n"
    | UNKNOWN -> Printf.printf "unknown: %s\n"
                   (Solver.get_reason_unknown solver)
  end

let make_id_from_apply fname args =
  (fname ^ "_" ^
   (String.concat ~sep:"_"
      (List.map args ~f:Ir.render_tterm)))

let register_symbs_z3 sttmts ctx ints =
  let var_map = ref String.Map.empty in
  let fun_map = ref String.Map.empty in
  let add_var vname =
    match String.Map.find !var_map vname with
    | Some _ -> ()
    | None -> var_map := String.Map.add !var_map ~key:vname
          ~data:(Expr.mk_const ctx
                   (mk_string ctx vname) ints)
  in
  let add_fun fname args =
    add_var (make_id_from_apply fname args);
    let really_add () =
      let domain = List.map args ~f:(fun _ -> ints) in
      fun_map := String.Map.add !fun_map ~key:fname
          ~data:((mk_fresh_func_decl ctx fname domain ints),args);
    in
    match String.Map.find !fun_map fname with
    | Some (f,old_args) ->
      if (List.length old_args) < (List.length args) then
        really_add ()
    | None -> really_add ()
  in
  List.iter sttmts ~f:(fun sttmt ->
      ignore (Ir.call_recursively_on_term (function
      | Ir.Id x -> add_var x;
        None
      | Ir.Apply (fname,args) ->
        add_fun fname args;
        None
      | Ir.Str_idx (arg,fname) -> add_fun fname [arg]; None
      | _ -> None) sttmt));
  (!var_map,!fun_map)

let tterm_to_z3 tterm ctx var_map fun_map ints =
  let rec run_on tterm = 
    match tterm.Ir.v with
    | Ir.Bop (op,lhs,rhs) ->
      let lhs = run_on lhs in
      let rhs = run_on rhs in
      begin match op with
        | Ir.Eq -> Boolean.mk_eq ctx lhs rhs
        | Ir.Le -> Arithmetic.mk_le ctx lhs rhs
        | Ir.Lt -> Arithmetic.mk_lt ctx lhs rhs
        | Ir.Ge -> Arithmetic.mk_ge ctx lhs rhs
        | Ir.Gt -> Arithmetic.mk_gt ctx lhs rhs
        | Ir.Add -> Arithmetic.mk_add ctx [lhs;rhs]
        | Ir.Sub -> Arithmetic.mk_sub ctx [lhs;rhs]
        | Ir.Mul -> Arithmetic.mk_mul ctx [lhs;rhs]
        | Ir.And -> Boolean.mk_and ctx [lhs;rhs]
      end
    | Ir.Apply (fname,args) ->
      let (f,max_args) = String.Map.find_exn fun_map fname in
      if (List.length args) < (List.length max_args) then
        String.Map.find_exn var_map (make_id_from_apply fname args)
      else
        Expr.mk_app ctx f (List.map args ~f:run_on)
  | Ir.Id x -> String.Map.find_exn var_map x
  | Ir.Struct (_,_) -> failwith ("no structures for a moment: " ^
                                 (Ir.render_tterm tterm))
  | Ir.Int i -> Expr.mk_numeral_int ctx i ints
  | Ir.Bool b -> Expr.mk_numeral_int ctx (if b then 1 else 0) ints
  | Ir.Not ({Ir.t=_;Ir.v=Ir.Apply _} as x) ->
    run_on {Ir.t=Ir.Boolean;
            Ir.v=Ir.Bop (Ir.Eq,
                         {Ir.t=x.Ir.t;Ir.v=Ir.Int 0},
                         x)}
  | Ir.Not x -> Boolean.mk_not ctx (run_on x)
  | Ir.Str_idx (x,fname) -> run_on {Ir.t=tterm.Ir.t;
                                 Ir.v=Ir.Apply (fname,[x])}
  | Ir.Deref _ -> failwith "no support for dereferences"
  | Ir.Fptr _ -> failwith "no support for fptrs"
  | Ir.Addr _ -> failwith "no spport for addrtaking"
  | Ir.Cast (_,tt) -> run_on tt
  | Ir.Undef -> failwith "what should I do with undef?"
  in
  run_on tterm

let struct_eq_to_z3 ctx (fields : Ir.var_spec list) term funs vars ints =
  let subterms = List.map fields ~f:(fun {name;value} ->
      let (f,_) = String.Map.find_exn funs name in
      Boolean.mk_eq ctx (Expr.mk_app ctx f [term]) (tterm_to_z3 value ctx vars funs ints))
  in
  Boolean.mk_and ctx subterms

let statement_to_z3 sttmt ctx vars funs ints =
  match sttmt.Ir.v with
  | Ir.Bop (Ir.Eq,{Ir.t=_;Ir.v=Ir.Struct (_,_)},_)
  | Ir.Bop (Ir.Eq,_,{Ir.t=_;Ir.v=Ir.Struct (_,_)}) ->
    failwith ("no support for structural equality: " ^ (Ir.render_tterm sttmt))
    (* struct_eq_to_z3 ctx fields (tterm_to_z3 x ctx vars funs ints) funs vars ints *)
  | Ir.Bop _ -> tterm_to_z3 sttmt ctx vars funs ints
  | Ir.Not _ -> tterm_to_z3 sttmt ctx vars funs ints
  | Ir.Apply _ -> tterm_to_z3 {Ir.t=Unknown;
                               Ir.v=Ir.Bop (Ir.Eq,
                                            {Ir.t=Unknown;Ir.v=Ir.Int 1},
                                            sttmt)}
                    ctx vars funs ints
  | Ir.Bool true -> Boolean.mk_true ctx
  | _ -> failwith ("incorrect statement " ^ (Ir.render_tterm sttmt))

let check_implication assumptions assertion =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in
  let ints = Integer.mk_sort ctx in
  let (vars,funs) = register_symbs_z3 (assertion::assumptions) ctx ints in
  show_vars vars; show_funs funs;
  let assumptions = List.map assumptions ~f:(fun ass -> statement_to_z3 ass ctx vars funs ints) in
  let negation = statement_to_z3 {Ir.v=Ir.Not assertion;Ir.t=Ir.Boolean}
      ctx vars funs ints
  in
  show_assumptions assumptions; show_negation negation;
  let solver = Solver.mk_solver ctx None in
  List.iter assumptions ~f:(fun ass -> Solver.add solver [ass]);
  Solver.add solver [negation];
  let result = (Solver.check solver []) in
  show_result result solver;
  match result with
  | SATISFIABLE -> false
  | UNSATISFIABLE -> true
  | UNKNOWN -> false


let is_assignment_justified assignment (assumptions : Ir.tterm list) =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in
  let ints = Integer.mk_sort ctx in
  let (vars,funs) = register_symbs_z3 (assignment::assumptions) ctx ints in
  show_vars vars; show_funs funs;
  let assumptions = List.map assumptions ~f:(fun ass -> statement_to_z3 ass ctx vars funs ints) in
  let assgn = statement_to_z3 assignment ctx vars funs ints in
  show_assumptions assumptions; show_assignment assgn;
  let solver = Solver.mk_solver ctx None in
  List.iter assumptions ~f:(fun ass -> Solver.add solver [ass]);
  Solver.add solver [assgn];
  let result = (Solver.check solver []) in
  show_result result solver;
  match (Solver.check solver []) with
  | SATISFIABLE -> true
  | UNSATISFIABLE -> false
  | UNKNOWN -> false

let is_assertion_justified (assertion:Ir.tterm) (assumptions : Ir.tterm list) =
  let cfg = [("model", "true"); ("proof", "false")] in
  let ctx = (mk_context cfg) in
  let ints = Integer.mk_sort ctx in
  let (vars,funs) = register_symbs_z3 (assertion::assumptions) ctx ints in
  show_vars vars; show_funs funs;
  let assumptions = List.map assumptions ~f:(fun ass -> statement_to_z3 ass ctx vars funs ints) in
  let hypothesis = statement_to_z3 assertion ctx vars funs ints in
  let theorem = Boolean.mk_not ctx hypothesis in
  show_assumptions assumptions;
  show_theorem theorem;
  let solver = Solver.mk_solver ctx None in
  List.iter assumptions ~f:(fun ass -> Solver.add solver [ass]);
  Solver.add solver [theorem];
  let result = (Solver.check solver []) in
  show_result result solver;
  match result with
  | SATISFIABLE -> false
  | UNSATISFIABLE -> true
  | UNKNOWN -> false
