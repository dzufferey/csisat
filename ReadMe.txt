CSIsat is an open-source interpolating decision procedure for LA+EUF.

Usage:
Reads the query from stdin and writes the result to stdout.

If the input formula is satisfiable, 
CSIsat writes "Satisfiable: <formula>" on stderr.
'formula' implies the conjunction of the two input formula.
Otherwise it writes an interpolant to stdout.

Options:
--------
-debug   Print debug information.
-check   Check the computed interpolant.
-sat     Check for satisfiability only (no interpolation).
         Writes only "satisfiable" or "unsatisfiable" to stdout.
-LAsolver Choose the LA solver to use.
         Options: simplex, simplex_wo_presolve, interior (default: simplex).
-SATsolver Choose the SAT solver to use.
         Options: csi_dpll, pico (default: csi_dpll). The PicoSAT integration is experimental.
-help    Display this list of options.
-syntax  Choose the syntax to use.
         Options: foci, infix (default: foci).
-round Try to round the coefficient to integer values. WARNING: has a limited precision.


Input language:
---------------
The language is similar to Foci.

query   ::  formula ; formula ; ... ; formula

formula :: '=' term term
         | '<=' term term
         | '&' '[' formula ... formula ']'
         | '|' '[' formula ... formula ']'
         | '~' formula

term    :: variable
         | '+' '[' term ... term ']'
         | '*' number term
         | function_symbol '[' term ... term ']'

'number' is an integer, floating point, or a ratio (number '/' number).

There is also an infix syntax:

query   ::  formula ; formula ; ... ; formula

formula :: term '=' term
         | term '<=' term
         | term '<' term
         | formula -> formula
         | formula <-> formula
         | formula & formula
         | formula | formula
         | 'not' formula

term    :: variable
         | term '+' term
         | term '-' term
         | number '*' term
         | '-' term
         | function_symbol '(' term , ... , term ')'

(precedence levels are [->,<->], [&,|], [not]. They are parsed as
left-associative.)

Authors: Dirk Beyer, Damien Zufferey, and Rupak Majumdar
