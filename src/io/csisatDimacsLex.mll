{
  open CsisatDimacsParse
}

let word = ['a'-'z' 'A'-'Z']+
let digit = ['0'-'9']
let num = '-'? ['1'-'9'] digit*
let white = [' ' '\t' '\n']
let zero = '0'

rule token = parse
  | 'p' white+ (word as form)           { P form }     (* skip header *)
  | num                                 { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | zero                                { ZERO }
  | white+                              { token lexbuf }     (* skip blanks *)
  | 'c' [^'\n']* '\n'                   { token lexbuf }     (* skip comments *)
  | eof                                 { EOF }
