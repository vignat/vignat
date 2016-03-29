open Core.Std
open Parser_util

type verification_outcome = Valid | Invalid of string

let verify_file fname =
  let _ = Sys.command ("~/proj/verifast-1757/bin/verifast -c -I ../nat " ^ fname ^ " > log.txt")
  in
  let vf_succeded = Sys.command ("grep '0 errors found' log.txt") in
  if vf_succeded = 0 then Valid
  else Invalid "see log.txt"

let export_assumptions src_file export_point assu_file =
  let _ = (* locate the line to dump VeriFast assumptions *)
    Sys.command ("sed -n '/" ^ export_point ^ "/=' " ^
                 src_file ^ " > export_lino.int ")
  in
  let export_lino = String.strip (In_channel.read_all "export_lino.int") in
  let _ =
    Sys.command ( "~/proj/verifast-1757/bin/verifast -c -I ../nat " ^
                  " -exportpoint " ^ export_lino ^
                  " -context_export_file " ^ assu_file ^ " " ^
                  src_file )
  in
  parse_file assu_file
