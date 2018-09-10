{
open Reader
open Lexing

let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
				Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
				Lexing.pos_bol = pos.Lexing.pos_cnum;
			      }

let error_msg pos msg =
  Printf.sprintf "%s:%d:%d: %s\n" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1) msg

let parse_error pos =
  prerr_endline (error_msg pos "Bad token");
  raise Parsing.Parse_error
}
let special = ['*' '/' '<' '=' '>' '!' '?' ':' '$' '%' '_' '&' '~' '^']
let start = ['a' - 'z' 'A' - 'Z'] | special
let part = start | ['-' '+' '0' - '9']
rule token = parse
     [' ' '\t']				{ token lexbuf }
  |  ['\n']				{ incr_linenum lexbuf; token lexbuf }
  | ';' [^ '\n']*			{ token lexbuf }
  | start part* as s                    { SYM(s) }
  | ['-' '+']? ['0'-'9']+ as n          { NUM(int_of_string n) }
  | ['"'] [^ '\\' '"']* ['"'] as s	{ STR(s) }
  | '('                         	{ LPAR }
  | ')'                         	{ RPAR }
  | eof                         	{ EOF }
  | _					{ parse_error (lexeme_start_p lexbuf) }
