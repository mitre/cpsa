%{

open Sexpr_type
open Lexing

let parse_error s =
  prerr_endline s
%}

%token <string> SYM STR
%token <int> NUM
%token LPAR RPAR EOF

%type <Lexing.position Sexpr_type.sexpr> top one sexpr
%type <Lexing.position Sexpr_type.sexpr list> list
%start top one
%%
top:
    sexpr			{ $1 }
  | EOF                         { raise End_of_file }
;
one:
    sexpr EOF			{ $1 }
;
sexpr:
    LPAR list RPAR              { L(symbol_start_pos (), List.rev $2) }
  | SYM                         { S(symbol_start_pos (), $1) }
  | STR                         { Q(symbol_start_pos (), $1) }
  | NUM                         { N(symbol_start_pos (), $1) }
;
list:
    list sexpr			{ $2 :: $1 }
  |                             { [] }
;
