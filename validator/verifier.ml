open Core.Std
open Parser_util

type verification_outcome = Valid | Invalid of string

let verify_file verifast fname outf =
  let _ = Sys.command (verifast ^ " -c -I ../nat " ^ fname ^ " > " ^ outf)
  in
  let vf_succeded = Sys.command ("grep '0 errors found' " ^ outf ^ " > /dev/null") in
  if vf_succeded = 0 then Valid
  else
    let unproven_assertion =
      Sys.command ("grep 'Assertion might not hold' " ^ outf ^ " > /dev/null")
    in
    let err = In_channel.read_all outf in
    if unproven_assertion = 0 then Invalid "Can not prove assertion"
    else Invalid err

let export_assumptions verifast src_file export_point assu_file lino_fname outf =
  let _ = (* locate the line to dump VeriFast assumptions *)
    Sys.command ("sed -n '/" ^ export_point ^ "/=' " ^
                 src_file ^ " > " ^ lino_fname)
  in
  let export_lino = String.strip (In_channel.read_all lino_fname) in
  let _ =
    Sys.command ( verifast ^ " -c -I ../nat " ^
                  " -exportpoint " ^ export_lino ^
                  " -context_export_file " ^ assu_file ^ " " ^
                  src_file ^ " > " ^ outf )
  in
  parse_file assu_file
