{
  open Lexing
  open Parser

  exception SyntaxError of string
  exception ReservedKeyword of string 

  (* From: https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                 pos_lnum = pos.pos_lnum + 1
      }

  let get_line lexbuf = lexbuf.lex_curr_p.pos_lnum
}

let identifier = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']*
let int     = ['0'-'9']+
let float   = ['0'-'9']+'.'['0'-'9']*
let whitespace = [' ' '\t']
let eol        = '\r' | '\n' | "\r\n" | "\n\r"

rule tokenize =
  parse
  (* whitespace and line endings *)
  | whitespace           { tokenize lexbuf }
  | eol                  { next_line lexbuf
                         ; tokenize lexbuf }
  (* End of Command *)
  | ';'                  { EOC }
  (* Operators *)
  | '+'                  { PLUS(get_line lexbuf) }
  | '-'                  { MINUS(get_line lexbuf) }
  | '/'                  { DIV(get_line lexbuf) }
  | '%'                  { MODULO(get_line lexbuf) }
  | "::"                 { CONCAT(get_line lexbuf) }
  (* Comparators *)
  | "=="                 { EQUALS(get_line lexbuf) }
  | "!="                 { NEQUALS(get_line lexbuf) }
  | '<'                  { LESS(get_line lexbuf) }
  | '>'                  { GREATER(get_line lexbuf) }
  | "<="                 { LESSEQ(get_line lexbuf) }
  | ">="                 { GREATEQ(get_line lexbuf) }
  | '?'                  { QMARK(get_line lexbuf) }
  (* Parentheses *)
  | '('                  { LPAREN(get_line lexbuf) }
  | ')'                  { RPAREN(get_line lexbuf) }
  | '{'                  { LBRACKET(get_line lexbuf) }
  | '}'                  { RBRACKET(get_line lexbuf) }
  | '['                  { LSQUAREB(get_line lexbuf) }
  | ']'                  { RSQUAREB(get_line lexbuf) }
  | "[]"                 { NIL(get_line lexbuf) }
  (* Keywords *)
  | "let"                { LET(get_line lexbuf) }
  | '='                  { ASSIGN(get_line lexbuf) }
  | "mut"                { MUT }
  | "while"              { WHILE(get_line lexbuf) }
  | "if"                 { IF(get_line lexbuf) }
  | "else"               { ELSE(get_line lexbuf) }
  | "skip"               { SKIP(get_line lexbuf) }
  | "return"             { RETURN(get_line lexbuf) }
  (* Type *)
  | ':'                  { COLON(get_line lexbuf) }
  | '*'                  { STAR(get_line lexbuf) }
  | ','                  { COMMA }
  (* Annotation and logic *)
  | "precondition"       { PRECONDITION(get_line lexbuf) }
  | "postcondition"      { POSTCONDITION(get_line lexbuf) }
  | "invariant"          { INVARIANT(get_line lexbuf) }
  | "termination"        { TERMINATION(get_line lexbuf) }
  | "forall"             { FORALL }
  | "exists"             { EXISTS }
  | '!'                  { NOT(get_line lexbuf) }
  | "/\\"                { AND(get_line lexbuf) }
  | "&&"                 { AND(get_line lexbuf) }
  | "\\/"                { OR(get_line lexbuf) }
  | "||"                 { OR(get_line lexbuf) }
  | "==>"                { IMPLIES(get_line lexbuf) }
  (* Differential Privacy *)
  | "epsilon"            { EPSILON(get_line lexbuf) }
  | "v_epsilon"          { EPSILONVAR(get_line lexbuf) }
  | "^"                  { DIST(get_line lexbuf) }
  (*  *)
  | "true"               { BOOL(true) }
  | "false"              { BOOL(false) }
  | identifier as lxm    { IDENTIFIER(lxm) }
  | int as lxm           { INT(int_of_string lxm) }
  | float as lxm         { FLOAT(float_of_string lxm) }
  (* Other *)
  | eof                  { EOF }
  | _                    { raise (SyntaxError ("Syntax Error: " ^ Lexing.lexeme lexbuf)) }
