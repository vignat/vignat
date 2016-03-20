%{
open Assumption

let args_to_string args =
  String.concat ", " (List.map term_to_string args)

%}

%token <int> INT
%token <string> ID
%token <bool> BOOL
%token COMMA
%token LPAREN
%token RPAREN
%token BANG
%token <Assumption.cmp> CMP
%token <char> BAOP
%token EOF

%right BAOP CMP BANG

%start <Assumption.term list> assumption_list

%%

assumption_list:
  | EOF { [] }
  | LPAREN; a = term; RPAREN; lst = assumption_list
        { a::lst }
  ;

term:
  | LPAREN; a = term; RPAREN             { a }
  | lhs = term; p = CMP; rhs = term      { Cmp (p, lhs, rhs) }
  | BANG; a = term;                      { Not a }
  | b = BOOL                             { Bool b }
  | i = INT                              { Int i }
  | i = ID                               { Id i }
  | f = ID; LPAREN; al = arg_list; RPAREN
                    { Id (f ^ "(" ^ (args_to_string al) ^ ")") }
  | lhs = term; op = BAOP; rhs = term
                    { Id ((term_to_string lhs) ^ " " ^
                          (String.make 1 op) ^ " " ^ (term_to_string rhs)) }
  ;

arg_list: al = separated_list(COMMA, term) { al };
