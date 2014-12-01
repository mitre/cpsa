%{

open Sexpr_type
open Lexing

let error_msg pos msg =
  Printf.sprintf "%s:%d:%d: %s\n" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1) msg

let parse_err pos s =
  prerr_endline (error_msg pos s);
  raise Parsing.Parse_error

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
  | RPAR                        { parse_err (symbol_start_pos ())
                                            "Unmatched right parenthesis" }
;
one:
    sexpr EOF			{ $1 }
  | RPAR                        { parse_err (symbol_start_pos ())
                                            "Unmatched right parenthesis" }
;
sexpr:
    LPAR list RPAR              { L(symbol_start_pos (), List.rev $2) }
  | SYM                         { S(symbol_start_pos (), $1) }
  | STR                         { Q(symbol_start_pos (), $1) }
  | NUM                         { N(symbol_start_pos (), $1) }
;
list:
    list sexpr			{ $2 :: $1 }
  | EOF                         { parse_err (symbol_start_pos ())
                                            "Missing right parenthesis" }
  |                             { [] }
;
