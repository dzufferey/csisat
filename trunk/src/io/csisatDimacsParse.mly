%token <int> NUM
%token <string> P
%token ZERO
%token EOF
%token EOL
%{
  module Ast = CsisatAst
%}
%start main             /* the entry point */
%type <string * int * int * (CsisatAst.predicate list list)> main
%%
main:
    P NUM NUM clauses       { ($1, $2, $3, $4) }
;
clauses:
    EOF                     { [] }
  | clause clauses          { $1 :: $2 }
;
clause:
    ZERO                    { [] }
  | NUM clause              { (if $1 < 0 then
                                Ast.Not (Ast.Atom (Ast.External (string_of_int (-$1))))
                               else
                                Ast.Atom (Ast.External (string_of_int $1))
                              ):: $2
                            }
;
