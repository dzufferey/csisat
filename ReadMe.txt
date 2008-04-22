CSIsat is an open-source interpolating decision procedure for LA+EUF.

Usage:
Reads the query from stdin and writes the result to stdout.

If the input formula is satisfiable, 
CSIsat writes "Satisfiable: <formula>" on stderr.
'formula' implies the conjunction of the two input formula.
Otherwise it writes an interpolant to stdout.

Options:
--help   Print this information.
-debug   Print debug information.
-check   Check the computed interpolant.
-sat     Check for satisfiability only (no interpolation).
         Writes only "satisfiable" or "unsatisfiable" to stdout.
-LAsolver Choose the LA solver to use.
         Options: simplex, simplex_wo_presolve, interior (default: simplex).
-SATsolver Choose the SAT solver to use.
         Options: csi_dpll, pico (default: csi_dpll). The PicoSAT integration is experimental.
-help  Display this list of options.
--help  Display this list of options.

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
