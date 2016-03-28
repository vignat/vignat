%{
open Ir
%}

%token <int> INT
%token <string> ID
%token <bool> BOOL
%token COMMA
%token LPAREN
%token RPAREN
%token EXEC
%token LCBR
%token RCBR
%token BANG
%token <Ir.bop> BOP
%token EOF

%right BOP BANG

%start <(Ir.tterm list) list> execution_list

%%

execution_list:
  | EOF { [] }
  | EXEC; LCBR; al = assumption_list; RCBR;
    lst = execution_list
        { al::lst }

assumption_list:
  | LPAREN; a = term; RPAREN; { [{v=a;t=Ir.Boolean}] }
  | LPAREN; a = term; RPAREN; lst = assumption_list
        { {v=a;t=Ir.Boolean}::lst }
  ;

term:
  | LPAREN; a = term; RPAREN             { a }
  | lhs = tterm; p = BOP; rhs = tterm    { Bop (p, lhs, rhs) }
  | BANG; a = tterm;                     { Not a }
  | b = BOOL                             { Bool b }
  | i = INT                              { Int i }
  | i = ID                               { Id i }
  | f = ID; LPAREN; al = arg_list; RPAREN
                    { Apply (f, al) }
  ;

tterm:
  | tr = term {{v=tr;t=Unknown}}

arg_list: al = separated_list(COMMA, tterm) { al };
