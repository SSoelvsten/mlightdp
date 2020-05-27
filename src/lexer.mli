exception SyntaxError of string;;

val tokenize: Lexing.lexbuf -> Parser.token;;
