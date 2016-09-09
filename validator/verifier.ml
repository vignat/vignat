open Core.Std
open Parser_util

type verification_outcome = Valid | Inconsistent | Invalid of string

let verify_file verifast fname outf proj_root export_point lino_fname=
  let _ = Sys.command (verifast ^ " -c -I " ^ proj_root ^
                       " " ^ fname ^ " > " ^ outf)
  in
  let vf_succeded = Sys.command ("grep '0 errors found' " ^ outf ^ " > /dev/null") in
  if vf_succeded = 0 then
    let _ = (* locate the line to dump VeriFast assumptions *)
      Sys.command ("sed -n '/" ^ export_point ^ "/=' " ^
                   fname ^ " > " ^ lino_fname)
    in
    let export_lino = String.strip (In_channel.read_all lino_fname) in
    let _ = Sys.command (verifast ^ " -c -I " ^ proj_root ^
                         " -breakpoint " ^ export_lino ^
                         " " ^ fname ^ " > " ^ outf)
    in
    let consistent = Sys.command ("grep 'Breakpoint reached' " ^ outf ^
                                  " > /dev/null")
    in
    if consistent = 0 then Valid
    else Inconsistent
  else
    let unproven_assertion =
      Sys.command ("grep 'Assertion might not hold' " ^ outf ^ " > /dev/null")
    in
    let err = In_channel.read_all outf in
    if unproven_assertion = 0 then Invalid "Can not prove assertion"
    else Invalid err

let export_assumptions
    verifast src_file export_point assu_file lino_fname outf proj_root =
  let _ = (* locate the line to dump VeriFast assumptions *)
    Sys.command ("sed -n '/" ^ export_point ^ "/=' " ^
                 src_file ^ " > " ^ lino_fname)
  in
  let export_lino = String.strip (In_channel.read_all lino_fname) in
  let _ =
    Sys.command ( verifast ^ " -c -I " ^ proj_root ^
                  " -exportpoint " ^ export_lino ^
                  " -context_export_file " ^ assu_file ^ " " ^
                  src_file ^ " > " ^ outf )
  in
  parse_file assu_file
