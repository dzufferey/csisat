CSIsat is an open-source interpolating decision procedure for LA+EUF.

Usage:
Reads the query from stdin and writes the answer to stdout.

If the input formula is satisfiable, 
CSIsat writes "Satisfiable: <formula>" on stderr.
'formula' implies the conjunction of the two input formula.
Otherwise it writes an interpolant to stdout.

Options:
-debug   Print debug information.
-check   Check the computed interpolant.
-sat     Check for satisfiability only (no interplolation).
         Writes only "satisfiable" or "unsatisfiable" to stdout.
-solver  Choose which LA solver to use.
         Options: simplex, simplex_wo_presolve, interior (default: simplex).

Input language:
The language is similar to Foci.

query   ::  formula ; formula

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
Warning: For the moment, "_1" is recognized as integer 1.

Authors: Dirk Beyer, Damien Zufferey, and Rupak Majumdar
