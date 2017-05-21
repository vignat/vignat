open Core
open Ir

type lemma_params = {ret_name: string; ret_val: string;
                     args: string list;
                     arg_exps: tterm list;
                     tmp_gen: string -> string;
                     is_tip: bool; arg_types: ttype list;
                     exptr_types: ttype String.Map.t;
                     ret_type: ttype}

type blemma_params = {args: string list;
                      arg_exps: tterm list;
                      tmp_gen: string -> string;
                      is_tip: bool; arg_types: ttype list;
                      exptr_types: ttype String.Map.t;
                      ret_type: ttype}

type lemma = (lemma_params -> string)
type blemma = (blemma_params -> string)

let tx_l str = (fun _ -> "/*@ " ^ str ^ " @*/" )
let tx_bl str = (fun _ -> "/*@ " ^ str ^ " @*/" )


let on_rez_nonzero str = (fun params ->
    "/*@ if(" ^ params.ret_name ^ "!=0) " ^ str ^ "@*/")

let on_rez_nz f = (fun params ->
    "/*@ if(" ^ params.ret_name ^ "!=0) " ^ (f params) ^ " @*/")

let rec render_deep_assignment {lhs;rhs} =
  match rhs.t with
  | Str (name,fields) ->
    String.concat ~sep: "\n"
      (List.map fields
         ~f:(fun (name,t) ->
             render_deep_assignment {lhs={v=Str_idx (lhs, name);t};
                                     rhs={v=Str_idx (rhs, name);t}}))
  | Unknown -> "";
  | _ -> (render_tterm lhs) ^ " = " ^
         (render_tterm rhs) ^ ";"

let deep_copy (var : var_spec) =
  (render_deep_assignment {lhs={v=Id var.name;t=var.value.t};
                             rhs=var.value}) ^
  "\n"

type type_set = Static of ttype | Dynamic of (string*ttype) list

let stt types =
  List.map types ~f:(fun t -> Static t)

let estt ex_ptrs =
  List.map ex_ptrs ~f:(fun (name,t) -> (name,Static t))

type fun_spec = {ret_type: type_set; arg_types: type_set list;
                 extra_ptr_types: (string * type_set) list;
                 lemmas_before: blemma list; lemmas_after: lemma list;}

module type Spec =
sig
  val preamble  : string
  val fun_types : fun_spec Core.String.Map.t
  val fixpoints : Ir.tterm Core.String.Map.t
  val boundary_fun : string
  val finishing_fun : string
  val eventproc_iteration_begin : string
  val eventproc_iteration_end : string
  val user_check_for_complete_iteration : string
end

let spec : (module Spec) option ref = ref None
