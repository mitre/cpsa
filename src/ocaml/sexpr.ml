include Sexpr_type
open Format

let annotation = function
  | S(a, _) -> a
  | Q(a, _) -> a
  | N(a, _) -> a
  | L(a, _) -> a

let read_sexpr ch =
  let lexbuf = Lexing.from_channel ch in
  Reader.top Scanner.token lexbuf

let read_sexpr_from_string ch =
  let lexbuf = Lexing.from_string ch in
  Reader.one Scanner.token lexbuf

let rec sexpr_printer f x =
  match x with
  | S (_, s) -> pp_print_string f s
  | Q (_, s) -> pp_print_string f s
  | N (_, n) -> pp_print_int f n
  | L (_, xs) -> print_list f xs
and print_list f x =
  match x with
  | [] -> pp_print_string f "()"
  | x :: xs ->
      pp_print_string f "(";
      pp_open_box f 1;
      sexpr_printer f x;
      print_rest f xs
and print_rest f x =
  match x with
  | [] ->
      pp_close_box f ();
      pp_print_string f ")"
  | x :: xs ->
      pp_print_space f ();
      sexpr_printer f x;
      print_rest f xs

let print_sexpr ch x =
  let f = formatter_of_out_channel ch in
  sexpr_printer f x;
  pp_print_newline f ();
  pp_print_newline f ()
