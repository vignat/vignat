open Sexplib.Conv
open Core

module Sexp = Core.Sexp

type bop = Eq | Le | Lt | Ge | Gt
         | Add | Sub | Mul
         | And | Bit_and [@@deriving sexp]


type ttype = | Ptr of ttype
             | Sint64
             | Sint32
             | Sint16
             | Sint8
             | Uint64
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
             | Unknown [@@deriving sexp]

type term_util = Ptr_placeholder of int64 [@@deriving sexp]

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
          | Zeroptr
          | Undef
          | Utility of term_util [@@deriving sexp]
and tterm = {v:term; t:ttype} [@@deriving sexp]
and var_spec = {name: string; value:tterm} [@@deriving sexp]

type eq_condition = {lhs: tterm; rhs: tterm} [@@deriving sexp]

let rec ttype_to_str = function
  | Ptr c_type -> ttype_to_str c_type ^ "*"
  | Sint64 -> "int64_t" | Sint32 -> "int32_t" | Sint16 -> "int16_t" | Sint8 -> "int8_t"
  | Uint64 -> "uint64_t"| Uint32 -> "uint32_t"
  | Uint16 -> "uint16_t" | Uint8 -> "uint8_t"
  | Void -> "void" | Str (name, _) -> "struct " ^ name
  | Ctm name -> name | Fptr name -> name ^ "*" | Boolean -> "bool"
  | Unknown -> "???"
  | Sunknown -> "s??" | Uunknown -> "u??"

let is_void = function | Void -> true | _ -> false

let get_pointee = function | Ptr t -> t
                           | x -> failwith ((ttype_to_str x) ^
                                            " is not a plain pointer")
let is_pointer (tt: tterm) = 
  match tt.t with 
  | Ptr _ -> begin match tt.v with
             | Id _ -> true
             | _ -> false
             end
  | _ -> false
let is_pointer_t (t: ttype) = 
  match t with 
  | Ptr _ -> true
  | _ -> false

type fun_call_context = {
  extra_pre_conditions: eq_condition list;
  pre_lemmas:string list;
  application:term;
  post_lemmas:string list;
  ret_name:string option;
  ret_type:ttype;
  call_id:int;
} [@@deriving sexp]

type hist_call_result = {
  args_post_conditions:eq_condition list;
  ret_val:tterm;
  post_statements:tterm list;
} [@@deriving sexp]

type hist_call = {
  context:fun_call_context;
  result:hist_call_result;
} [@@deriving sexp]

type tip_call = {context:fun_call_context;
                 results:hist_call_result list} [@@deriving sexp]

type ir = {
  preamble:string;
  free_vars:var_spec String.Map.t; (* TODO: var_spec -> typed_var *)
  arguments:var_spec list; (*FIXME: holds also extra ptrs*)
  cmplxs:var_spec String.Map.t;
  context_assumptions:tterm list;
  hist_calls:hist_call list;
  tip_call:tip_call;
  export_point:string;
  finishing:bool;
  complete_event_loop_iteration:bool;
  semantic_checks:string;
} [@@deriving sexp]

let render_bop = function
  | Eq -> "=="
  | Le -> "<="
  | Lt -> "<"
  | Ge -> ">="
  | Gt -> ">"
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | And -> "&&"
  | Bit_and -> "&"

let render_utility = function
  | Ptr_placeholder addr -> "?placeholder addr:" ^ (Int64.to_string addr)

let int_type_postfix = function
  | Uint64 -> "ULL"
  | _ -> ""

let rec render_tterm (t:tterm) =
  match t.v with
  | Bop (op, lhs, rhs) -> "(" ^ (render_tterm lhs) ^
                          " " ^ (render_bop op) ^ " " ^
                          (render_tterm rhs) ^ ")"
  | Apply (fname,args) ->
    let arg_strings = List.map args ~f:render_tterm in
    fname ^ "(" ^ (String.concat ~sep:", " arg_strings) ^ ")"
  | Id name -> name;
  | Struct (_,fields) ->
    "{" ^ (String.concat ~sep:", "
             (List.map fields ~f:(fun {name;value} ->
                  "." ^ name ^ " = " ^ (render_tterm value)))) ^
    "}"
  | Int 0 -> if (t.t = Boolean) then "false" else ("0"^ (int_type_postfix t.t))
  | Int 1 -> if (t.t = Boolean) then "true" else ("1"^ (int_type_postfix t.t))
  | Int i -> string_of_int i ^ (int_type_postfix t.t)
  | Bool b -> string_of_bool b
  | Not t -> "!(" ^ (render_tterm t) ^ ")"
  | Str_idx ({v=Id x;t=_}, field_name) -> x ^ "." ^ field_name
  | Str_idx ({v=Str_idx ({v=Id x;t=_}, fname1);t=_}, fname2) ->
    x ^ "." ^ fname1 ^ "." ^ fname2
  | Str_idx ({v=Str_idx ({v=Str_idx ({v=Id x;t=_}, fname1);t=_},
                         fname2);t=_},
             fname3) ->
    x ^ "." ^ fname1 ^ "." ^ fname2 ^ "." ^ fname3
  | Str_idx ({v=Deref {v=Id x;t=_};t=_},field_name) -> x ^ "->" ^ field_name
  | Str_idx ({v=Deref x;_},field_name) -> "(" ^ (render_tterm x) ^ ")->" ^ field_name
  | Str_idx (t,field_name) -> "(" ^ (render_tterm t) ^ ")." ^ field_name
  | Deref t -> "*(" ^ (render_tterm t) ^ ")"
  | Fptr f -> f
  | Addr t -> "&(" ^ (render_tterm t) ^ ")"
  | Cast (t,v) -> "(" ^ ttype_to_str t ^ ")" ^ (render_tterm v)
  | Zeroptr -> "0"(*"NULL"*)
  | Undef -> "???"
  | Utility util -> render_utility util
and render_term t = render_tterm {v=t;t=Unknown} (*TODO: reformulate this coupled definition*)

let term_utility_eq a b =
  match a, b with
  | Ptr_placeholder x, Ptr_placeholder y -> (x = y)

let rec term_eq a b =
  match a,b with
  | Bop (Eq, lhsa, rhsa), Bop (Eq, lhsb, rhsb) ->
    ((term_eq lhsa.v lhsb.v) && (term_eq rhsa.v rhsb.v)) || ((term_eq lhsa.v rhsb.v) && (term_eq rhsa.v lhsb.v))
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
  | Utility ua, Utility ub -> term_utility_eq ua ub
  | _, _ -> false

let rec call_recursively_on_tterm (f:tterm -> tterm option) tterm =
  let tterm =
    {v= begin
        match tterm.v with
        | Bop (op,lhs,rhs) ->
          Bop (op, call_recursively_on_tterm f lhs, call_recursively_on_tterm f rhs)
        | Apply (fname,args) ->
          Apply (fname, List.map args ~f:(call_recursively_on_tterm f))
        | Id x -> Id x
        | Struct (name,fds) ->
          Struct (name,List.map fds ~f:(fun field ->
              {field with value = call_recursively_on_tterm f field.value}))
        | Int i -> Int i
        | Bool b -> Bool b
        | Not x -> Not (call_recursively_on_tterm f x)
        | Str_idx (tt,fname) -> Str_idx (call_recursively_on_tterm f tt,fname)
        | Deref tt -> Deref (call_recursively_on_tterm f tt)
        | Fptr fname -> Fptr fname
        | Addr tt -> Addr (call_recursively_on_tterm f tt)
        | Cast (ctype,tt) -> Cast (ctype,call_recursively_on_tterm f tt)
        | Undef -> Undef
        | Zeroptr -> Zeroptr
        | Utility u -> Utility u
      end;
     t=tterm.t} in
  match f tterm with
  | Some tt -> tt
  | None -> tterm

let call_recursively_on_term (f:term -> term option) tterm =
  call_recursively_on_tterm (fun {v;t} -> match f v with
      | Some v -> Some {v;t}
      | None -> None) tterm

let simplify_tterm tterm =
  call_recursively_on_term (function
      | Deref {t=_;v=Addr x} -> Some x.v
      | Str_idx ({v=Struct (_,fields);
                  t=_},
                 fname) ->
        let field =
          List.find_exn fields ~f:(fun {name;value=_} ->
              String.equal name fname)
        in
        Some field.value.v
      | _ -> None) tterm

let rec replace_tterm old_tt new_tt tterm =
  if tterm = old_tt then new_tt else 
  match tterm.v with
  | Bop (opa, lhs, rhs) -> {v=Bop (opa, replace_tterm old_tt new_tt lhs, replace_tterm old_tt new_tt rhs);t=tterm.t}
  | Apply (f, args) -> {v=Apply(f, List.map args ~f:(replace_tterm old_tt new_tt));t=tterm.t}
  | Struct (name, fields) -> {v=Struct (name, List.map fields ~f:(fun fi -> {fi with value = replace_tterm old_tt new_tt fi.value}));t=tterm.t}
  | Not tt -> {v=Not (replace_tterm old_tt new_tt tt);t=tterm.t}
  | Str_idx (term, field) -> {v=Str_idx (replace_tterm old_tt new_tt term, field);t=tterm.t}
  | Deref tt -> {v=Deref (replace_tterm old_tt new_tt tt);t=tterm.t}
  | Addr tt -> {v=Addr (replace_tterm old_tt new_tt tt);t=tterm.t}
  | Cast (ct, tt) -> {v=Cast (ct, replace_tterm old_tt new_tt tt);t=tterm.t}
  | Utility _
  | Fptr _
  | Undef
  | Zeroptr
  | Id _
  | Int _
  | Bool _ -> tterm


let rec append_id_in_term_id_starting_with prefix suffix term = match term with
  | Bop (opa, lhs, rhs) -> Bop(opa, append_id_in_tterm_id_starting_with prefix suffix lhs, append_id_in_tterm_id_starting_with prefix suffix rhs)
  | Apply (f, args) -> Apply(f, List.map args ~f:(append_id_in_tterm_id_starting_with prefix suffix))
  | Id x -> if String.is_prefix x ~prefix:prefix then Id (x ^ suffix) else Id x
  | Struct _ -> failwith "not supported here, too lazy"
  | Int _ -> term
  | Bool _ -> term
  | Not tt -> Not (append_id_in_tterm_id_starting_with prefix suffix tt)
  | Str_idx (tterm, field) -> Str_idx (append_id_in_tterm_id_starting_with prefix suffix tterm, field)
  | Deref tterm -> Deref (append_id_in_tterm_id_starting_with prefix suffix tterm)
  | Fptr _ -> term
  | Addr tterm -> Addr (append_id_in_tterm_id_starting_with prefix suffix tterm)
  | Cast (ctype, tterm) -> Cast (ctype, append_id_in_tterm_id_starting_with prefix suffix tterm)
  | Undef -> Undef
  | Zeroptr -> Zeroptr
  | Utility _ -> term
and append_id_in_tterm_id_starting_with prefix suffix tterm =
  {tterm with v=(append_id_in_term_id_starting_with prefix suffix tterm.v)}


let rec fix_type_of_id_in_tterm (vars: var_spec list) tterm = match tterm.v with
  | Bop (opa, lhs, rhs) -> {v=Bop(opa, fix_type_of_id_in_tterm vars lhs, fix_type_of_id_in_tterm vars rhs);t=tterm.t}
  | Apply (f, args) -> {v=Apply(f, List.map args ~f:(fix_type_of_id_in_tterm vars));t=tterm.t}
  | Id x -> begin match List.find vars ~f:(fun v -> v.name = x) with
            | Some v -> {v=Id v.name;t=v.value.t}
            | None -> tterm end
  | Struct (name, fields) -> {v=Struct(name, List.map fields ~f:(fun vs -> {vs with value=fix_type_of_id_in_tterm vars vs.value}));t=tterm.t}
  | Int _ -> tterm
  | Bool _ -> tterm
  | Not tt -> {v=Not (fix_type_of_id_in_tterm vars tt);t=tterm.t}
  | Str_idx (tt, field) -> {v=Str_idx (fix_type_of_id_in_tterm vars tt, field);t=tterm.t}
  | Deref tt -> {v=Deref (fix_type_of_id_in_tterm vars tt);t=tterm.t}
  | Fptr _ -> tterm
  | Addr tt -> {v=Addr (fix_type_of_id_in_tterm vars tt);t=tterm.t}
  | Cast (ctype, tt) -> {v=Cast (ctype, fix_type_of_id_in_tterm vars tt);t=tterm.t}
  | Undef -> tterm
  | Zeroptr -> tterm
  | Utility _ -> tterm

let rec collect_nodes f tterm =
  match f tterm with
  | Some x -> [x]
  | None ->
    match tterm.v with
    | Bop (_,lhs,rhs) -> (collect_nodes f lhs) @ (collect_nodes f rhs)
    | Apply (_,args) -> List.join (List.map args ~f:(collect_nodes f))
    | Id _ -> []
    | Struct (_,fields) ->
      List.join (List.map fields ~f:(fun {name=_;value} ->
          collect_nodes f value))
    | Int _ -> []
    | Bool _ -> []
    | Not x -> collect_nodes f x
    | Str_idx (str,_) -> collect_nodes f str
    | Deref ptr -> collect_nodes f ptr
    | Fptr _ -> []
    | Addr v -> collect_nodes f v
    | Cast (_,v) -> collect_nodes f v
    | Undef -> []
    | Zeroptr -> []
    | Utility _ -> []

let rec is_const term =
  let is_utility_const = function
    | Ptr_placeholder _ -> false
  in
  match term with
  | Bop (_,lhs,rhs) -> (is_constt lhs) && (is_constt rhs)
  | Apply (_,args) -> List.for_all args ~f:is_constt
  | Id _ -> false
  | Struct (_,fields) -> List.for_all fields
                           ~f:(fun field -> is_constt field.value)
  | Int _ -> true
  | Bool _ -> true
  | Not t -> is_constt t
  | Str_idx (tterm,_) -> is_constt tterm
  | Deref tterm -> is_constt tterm
  | Fptr _ -> true
  | Addr tterm -> is_constt tterm
  | Cast (_,tterm) -> is_constt tterm
  | Undef -> true
  | Zeroptr -> true
  | Utility u -> is_utility_const u
and is_constt tterm = is_const tterm.v
