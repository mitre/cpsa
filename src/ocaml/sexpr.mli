type 'a sexpr =
  | S of 'a * string
  | Q of 'a * string
  | N of 'a * int
  | L of 'a * 'a sexpr list

val annotation : 'a sexpr -> 'a

val read_sexpr : in_channel -> Lexing.position sexpr

val read_sexpr_from_string : string -> Lexing.position sexpr

val sexpr_printer : Format.formatter -> 'a sexpr -> unit

val print_sexpr : out_channel -> 'a sexpr -> unit
