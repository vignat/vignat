open Core.Std
open Ir

let prepare_tasks ir =
  List.map ir.tip_call.results ~f:(fun result ->
      let exists_such =
        (List.map result.args_post_conditions
           ~f:(fun spec -> {v=Bop (Eq,{v=Id spec.name;t=Unknown},
                                   spec.value);
                            t=Boolean})) @
        result.post_statements
      in
      let exists_such =
        match ir.tip_call.context.ret_name with
        | Some ret_name ->
          {v=Bop (Eq,{v=Id ret_name;t=ir.tip_call.context.ret_type},
                  result.ret_val);t=Boolean} :: exists_such
        | None -> exists_such
      in
      {exists_such;
       filename="aaa.c";
       export_point=ir.export_point})

let validate_prefix fin fout =
  let ir = Import.build_ir fin in
  Render.render_ir ir fout;
  match Verifier.verify_file fout with
  | Verifier.Valid -> printf "Valid.\n"
  | Verifier.Invalid _ ->
    begin
      let vf_assumptions = Verifier.export_assumptions fout ir.export_point
          "assumptions.vf"
      in
      let ir = Analysis.induce_symbolic_assignments ir vf_assumptions in
      Render.render_ir ir fout;
      match Verifier.verify_file fout with
      | Verifier.Valid -> printf "Valid.\n"
      | Verifier.Invalid cause -> printf "Failed: %s\n" cause
    end

let () =
  validate_prefix Sys.argv.(1) Sys.argv.(2)
