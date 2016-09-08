open Core.Std
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

let output_queries = false

let show_vars vars =
  if output_queries then begin
    Printf.printf ";vars:\n";
    List.iter (Map.data vars) ~f:(fun v ->
        Printf.printf "(declare-fun %s () Int)\n" (Expr.to_string v))
  end

let show_funs funs =
  if output_queries then begin
    Printf.printf ";funs:\n";
    List.iter (Map.data funs) ~f:(fun f ->
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

let register_symbs_z3 sttmts ctx ints =
  let var_map = ref String.Map.empty in
  let fun_map = ref String.Map.empty in
  List.iter sttmts ~f:(fun sttmt ->
      ignore (Ir.call_recursively_on_tterm (function
      | Ir.Id x -> begin match String.Map.find !var_map x with
          | Some _ -> None
          | None -> var_map := String.Map.add !var_map ~key:x
                ~data:(Expr.mk_const ctx
                         (mk_string ctx x) ints);
            None
        end
      | Apply (fname,args) -> begin match String.Map.find !fun_map fname with
          | Some _ -> None
          | None ->
            let domain = List.map args ~f:(fun _ -> ints) in
            fun_map := String.Map.add !fun_map ~key:fname
                ~data:(mk_fresh_func_decl ctx fname domain ints);
            None
        end
      | _ -> None) sttmt));
  (!var_map,!fun_map)

let tterm_to_z3 tterm ctx var_map fun_map ints =
  let rec run tterm = 
    match tterm.Ir.v with
    | Ir.Bop (op,lhs,rhs) ->
      let lhs = run lhs in
      let rhs = run rhs in
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
      let f = String.Map.find_exn fun_map fname in
      Expr.mk_app ctx f (List.map args ~f:run)
  | Ir.Id x -> String.Map.find_exn var_map x
  | Ir.Struct (name,fds) -> failwith "no structures for a moment"
  | Ir.Int i -> Expr.mk_numeral_int ctx i ints
  | Ir.Bool b -> Expr.mk_numeral_int ctx (if b then 1 else 0) ints
  | Ir.Not x -> Boolean.mk_not ctx (run x)
  | Ir.Str_idx (tt,fname) -> failwith "no structure destructure for now"
  | Ir.Deref tt -> failwith "no support for dereferences"
  | Ir.Fptr fname -> failwith "no support for fptrs"
  | Ir.Addr tt -> failwith "no spport for addrtaking"
  | Ir.Cast (ctype,tt) -> run tt
  | Ir.Undef -> failwith "what should I do with undef?"
  in
  run tterm

let statement_to_z3 sttmt ctx funs vars ints =
  match sttmt.Ir.v with
  | Ir.Bop _ -> tterm_to_z3 sttmt ctx funs vars ints
  | Ir.Not _ -> tterm_to_z3 sttmt ctx funs vars ints
  | Ir.Apply _ -> tterm_to_z3 {Ir.t=Unknown;
                               Ir.v=Ir.Bop (Ir.Eq,
                                            {Ir.t=Unknown;Ir.v=Ir.Int 1},
                                            sttmt)}
                    ctx funs vars ints
  | Ir.Bool true -> Boolean.mk_true ctx
  | _ -> failwith ("incorrect statement " ^ (Ir.render_tterm sttmt))

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
