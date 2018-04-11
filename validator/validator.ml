open Core
open Ir

let validate_prefix fin intermediate_pref verifast_bin proj_root =
  let spec_mod =  match !Fspec_api.spec with
    | Some m -> m
    | None -> failwith "Failed: could not find function spec dynamic module"
  in
  let module Spec = (val spec_mod) in
  let assumptions_fname = intermediate_pref ^ ".assumptions.vf" in
  let lino_fname = intermediate_pref ^ ".lino.int" in
  let export_out_fname = intermediate_pref ^ ".export.stdout" in
  let verify_out_fname = intermediate_pref ^ ".verify.stdout" in
  let ir_fname = intermediate_pref ^ ".ir" in
  let intermediate_fout = intermediate_pref ^ ".c" in
  let export_fout = intermediate_pref ^ ".exprt.c" in
  ignore (Sys.command ("rm -f " ^
                       assumptions_fname ^ " " ^
                       lino_fname ^ " " ^
                       export_out_fname ^ " " ^
                       verify_out_fname ^ " " ^
                       ir_fname ^ " " ^
                       intermediate_fout ^ " " ^
                       export_fout));
  let ir =
    Import.build_ir Spec.fun_types fin Spec.preamble Spec.boundary_fun Spec.finishing_fun
      Spec.eventproc_iteration_begin Spec.eventproc_iteration_end
  in
  let ir = {ir with semantic_checks = if (ir.complete_event_loop_iteration) then
                        Spec.user_check_for_complete_iteration
                      else ""}
  in
  Out_channel.write_all ir_fname ~data:(Sexp.to_string (sexp_of_ir ir));
  match Verifier.verify_ir
          ir verifast_bin intermediate_fout verify_out_fname proj_root lino_fname
  with
  | Verifier.Valid -> printf "Valid.\n"
  | Verifier.Inconsistent -> printf "Inconsistent.\n"
  | Verifier.Invalid_seq -> printf "Invalid.\n"
  | Verifier.Invalid_rez _ -> printf "Invalid output.\n"

let load_plug fname =
  let fname = Dynlink.adapt_filename fname in
  match Sys.file_exists fname with
  | `No | `Unknown -> failwith ("Plugin file " ^ fname ^ " does not exist")
  | `Yes -> begin
      try Dynlink.loadfile fname
      with
      | (Dynlink.Error err) as e ->
        print_endline ("ERROR loading plugin: " ^ (Dynlink.error_message err) );
        raise e
      | _ -> failwith "Unknow error while loading plugin"
    end

let () =
  load_plug Sys.argv.(1);
  validate_prefix Sys.argv.(2) Sys.argv.(3) Sys.argv.(4) Sys.argv.(5)
