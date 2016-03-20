{
open Lexing
open Assumption_parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with pos_bol = lexbuf.lex_curr_pos;
                                  pos_lnum = pos.pos_lnum + 1 }
}

let int = '-'?['0'-'9']+
let white = [' ' '\t']+
let newline = ['\r' '\n']|"\r\n"
let id = ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule read =
  parse
       | white   {read lexbuf}
       | newline {next_line lexbuf; read lexbuf}
       | int     {INT (int_of_string (Lexing.lexeme lexbuf))}
       | "true"  {BOOL true}
       | "false" {BOOL false}
       | id      {ID (Lexing.lexeme lexbuf)}
       | ','     {COMMA}
       | '('     {LPAREN}
       | ')'     {RPAREN}
       | '<'     {CMP Lt}
       | '>'     {CMP Gt}
       | "<="    {CMP Le}
       | ">="    {CMP Ge}
       | '='     {CMP Eq}
       | "<==>"  {CMP Eq}
       | '-'     {BAOP '-'}
       | '+'     {BAOP '+'}
       | '!'     {BANG}
       | _       {raise (SyntaxError ("Unexpected char: " ^ (Lexing.lexeme lexbuf)))}
       | eof     {EOF}
