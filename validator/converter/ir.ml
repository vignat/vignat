open Sexplib.Conv
open Core.Std

module Sexp = Core.Std.Sexp

type bop = Eq | Le | Lt | Ge | Gt
         | Add | Sub
         | And with sexp


type ttype = | Ptr of ttype
             | Sint32
             | Uint32
             | Uint16
             | Uint8
             | Void
             | Str of string * (string * ttype) list
             | Ctm of string
             | Fptr of string
             | Boolean
             | Sunknown
             | Uunknown
             | Unknown
with sexp

type term = Bop of bop*tterm*tterm
          | Apply of string*tterm list
          | Id of string
          | Struct of string*var_spec list
          | Int of int
          | Bool of bool
          | Not of tterm
          | Str_idx of tterm*string
          | Deref of tterm
          | Addr of tterm
          | Fptr of string
          | Cast of ttype*tterm
          | Undef
and tterm = {v:term; t:ttype}
and var_spec = {name: string; value:tterm}
with sexp

let rec ttype_to_str = function
  | Ptr c_type -> ttype_to_str c_type ^ "*"
  | Sint32 -> "int" | Uint32 -> "uint32_t" | Uint16 -> "uint16_t"
  | Uint8 -> "uint8_t" | Void -> "void" | Str (name, _) -> "struct " ^ name
  | Ctm name -> name | Fptr name -> name ^ "*" | Boolean -> "bool" | Unknown -> "???"
  | Sunknown -> "s??" | Uunknown -> "u??"

let is_void = function | Void -> true | _ -> false

let get_pointee = function | Ptr t -> t | _ -> failwith "not a plain pointer"

type fun_call_context = {
  pre_lemmas:string list;
  application:term;
  post_lemmas:string list;
  ret_name:string option;
  ret_type:ttype;
} with sexp

type call_result = {
  args_post_conditions:var_spec list;
  ret_val:tterm;
  post_statements:tterm list;
} with sexp

type hist_call = {
  context:fun_call_context;
  result:call_result;
} with sexp

type tip_call = {context:fun_call_context;
                 results:call_result list} with sexp

type ir = {
  preamble:string;
  free_vars:var_spec String.Map.t;
  arguments:var_spec String.Map.t;
  tmps:var_spec String.Map.t;
  cmplxs:var_spec String.Map.t;
  context_assumptions:tterm list;
  hist_calls:hist_call list;
  tip_call:tip_call;
  leaks:string list;
} with sexp

type task = {
  path_constraints:tterm list;
  exists_such:tterm list;
  assert_lino:int;
} with sexp

let strip_outside_parens str =
  if (String.is_prefix str ~prefix:"(") &&
     (String.is_suffix str ~suffix:")") then
    String.chop_prefix_exn (String.chop_suffix_exn str ~suffix:")")
      ~prefix:"("
  else str

let render_bop = function
  | Eq -> "=="
  | Le -> "<="
  | Lt -> "<"
  | Ge -> ">="
  | Gt -> ">"
  | Add -> "+"
  | Sub -> "-"
  | And -> "&&"

let rec render_tterm (t:tterm) =
  match t.v with  (*strip parens: account for weird VeriFast parser*)
  | Bop (op, lhs, rhs) -> "(" ^ (strip_outside_parens (render_tterm lhs)) ^
                          " " ^ (render_bop op) ^ " " ^
                          (render_tterm rhs) ^ ")"
  | Apply (fname,args) ->
    let arg_strings = List.map args ~f:render_tterm in
    fname ^ "(" ^ (String.concat ~sep:", " arg_strings) ^ ")"
  | Id name -> name;
  | Struct (_,fields) ->
    "{" ^ (String.concat ~sep:", "
             (List.map fields ~f:(fun {name;value} ->
                  name ^ " = " ^ (render_tterm value)))) ^
    "}"
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | Not t -> "!(" ^ (render_tterm t) ^ ")"
  | Str_idx (t,field_name) -> "(" ^ (render_tterm t) ^ ")." ^ field_name
  | Deref t -> "*(" ^ (render_tterm t) ^ ")"
  | Fptr f -> f
  | Addr t -> "&(" ^ (render_tterm t) ^ ")"
  | Cast (t,v) -> "(" ^ ttype_to_str t ^ ")" ^ (render_tterm v)
  | Undef -> "???"
and render_term t = render_tterm {v=t;t=Unknown} (*TODO: reformulate this coupled definition*)

let rec term_eq a b =
  match a,b with
  | Bop (opa,lhsa,rhsa), Bop (opb,lhsb,rhsb) ->
    opa = opb && (term_eq lhsa.v lhsb.v) && (term_eq rhsa.v rhsb.v)
  | Apply (fa,argsa), Apply (fb, argsb) ->
    (String.equal fa fb) && ((List.length argsa) = (List.length argsb)) &&
    (List.for_all2_exn argsa argsb ~f:(fun arga argb -> term_eq arga.v argb.v))
  | Id a, Id b -> String.equal a b
  | Struct (sna,fdsa), Struct (snb,fdsb) ->
    (String.equal sna snb) && ((List.length fdsa) = (List.length fdsb)) &&
    (List.for_all2_exn fdsa fdsb ~f:(fun {name=fnamea;value=fvala}
                                      {name=fnameb;value=fvalb} ->
         (String.equal fnamea fnameb) &&
         term_eq fvala.v fvalb.v))
  | Int ia, Int ib -> ia = ib
  | Bool ba, Bool bb -> ba = bb
  | Not tta, Not ttb -> term_eq tta.v ttb.v
  | Str_idx (tta,fda), Str_idx (ttb,fdb) -> term_eq tta.v ttb.v && String.equal fda fdb
  | Deref tta, Deref ttb -> term_eq tta.v ttb.v
  | Fptr fa, Fptr fb -> String.equal fa fb
  | Addr tta, Addr ttb -> term_eq tta.v ttb.v
  | Cast (ctypea,terma), Cast (ctypeb,termb) -> (ctypea = ctypeb) && (term_eq terma.v termb.v)
  | Undef, Undef -> true
  | _, _ -> false

              (*
                let rec replace_term_in_term old_t new_t term =
                  if term_eq term old_t then new_t else
                    match term with
                    | Bop (opa,lhs,rhs) ->
                      Bop (opa,{v=replace_term_in_term old_t new_t lhs.v;t=lhs.t},
                           {v=replace_term_in_term old_t new_t rhs.v;t=rhs.t})
                    | Apply (f,args) -> Apply (f,replace_term_in_tterm_list old_t new_t args)
                    | Id x -> Id x
                    | Struct ()
              *)
