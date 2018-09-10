open Sexpr_type
open Lexing

type token = SYM of string | STR of string | NUM of int | LPAR | RPAR | EOF
val error_msg : position -> string -> string
val failwith_msg : position -> string -> 'a
val parse_err : position -> string -> 'a
val top : (lexbuf -> token) -> lexbuf -> position sexpr
val one : (lexbuf -> token) -> lexbuf -> position sexpr
