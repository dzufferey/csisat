{
  open InfixParse
}

let white = [' ' '\t' '\n']

let digit = ['0'-'9']
let num = '-'? digit+
let real = '-'? digit+ '.' digit*

let word = ['a'-'z' 'A'-'Z' '_']+
let ident = word (word | digit)*
let ident2 = ''' [^'\n' ''']+ '''

rule token = parse
  | "="             { EQ }
  | "<="            { LEQ }
  | '<'             { LT }
  | ">="            { GEQ }
  | '>'             { GT }
  | "->"            { IMPLIES }
  | "<->"           { IFF }
  | "not"           { NOT }
  | '&'             { AND }
  | '|'             { OR }
  | '+'             { PLUS }
  | '*'             { TIMES }
  | '/'             { SLASH }
  | real            { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | num             { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | '-'             { MINUS }
  | ';'             { SEMICOLON }
  | ','             { COMMA }
  | '['             { LBRACK }
  | ']'             { RBRACK }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | "true"          { TRUE }
  | "false"         { FALSE }
  | ident           { IDENT (Lexing.lexeme lexbuf) }
  | ident2          { IDENT (Lexing.lexeme lexbuf) }
  | white+          { token lexbuf } (* skip blanks *)
  | eof             { EOF }
