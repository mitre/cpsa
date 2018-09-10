open Lexing
open Format

type 'a sexpr =
  | S of 'a * string
  | Q of 'a * string
  | N of 'a * int
  | L of 'a * 'a sexpr list

val annotation : 'a sexpr -> 'a

val read_lexbuf : string -> in_channel -> lexbuf

val read_sexpr : lexbuf -> position sexpr

val read_sexpr_from_string : string -> position sexpr

val sexpr_printer : formatter -> 'a sexpr -> unit

val print_sexpr : out_channel -> 'a sexpr -> unit

val sym : string -> unit sexpr
val quo : string -> unit sexpr
val num : int -> unit sexpr
val lst : unit sexpr list -> unit sexpr

val strip : 'a sexpr -> unit sexpr
val assoc : string -> 'a sexpr list -> 'a sexpr list
val has_key : string -> 'a sexpr list -> bool
val rem_keys : string list -> 'a sexpr list -> 'a sexpr list
