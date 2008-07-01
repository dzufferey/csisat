{
  open FociParse
}

let word = ['a'-'z' 'A'-'Z' '_']+
let digit = ['0'-'9']
let num = '-'? digit+
let white = [' ' '\t' '\n']
let real = '-'? digit+ '.' digit*
let ident = word (word | digit)*
let ident2 = ''' [^'\n' ''']+ '''

rule token = parse
  | "="             { EQ }
  | "<="            { LEQ }
  | "<"             { LT }
  | '+'             { PLUS }
  | '*'             { TIMES }
  | "->"            { IMPLIES }
  | '~'             { NOT }
  | '/'             { SLASH }
  | '&'             { AND }
  | '|'             { OR }
  | ';'             { SEMICOLON }
  | '['             { LBRACK }
  | ']'             { RBRACK }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '#'             { SHARP }
  | '@'             { AT }
  | "true"          { TRUE }
  | "false"         { FALSE }
  | real            { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | num             { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | ident           { IDENT (Lexing.lexeme lexbuf) }
  | ident2          { IDENT (Lexing.lexeme lexbuf) }
  | white+          { token lexbuf } (* skip blanks *)
  | eof             { EOF }
