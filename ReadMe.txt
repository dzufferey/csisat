Requirements:
  - ocaml with the 'C' headers installed
  - glpk

Compilation:
just execute: make

Configuration:
The makefile makes the following assumptions:
  - The file 'libglpk.a' is located in '/usr/lib/'.
    If this is not the case, please modify the GLPK variable in the Makefile.
  - The ocaml headers and glpk headers are in the default include path.
    If this is not the case, please modify the Makefile for glpk,
    or glpk_ml_wrapper/Makefile for ocaml.
If you want to compile a statically linked version, uncomment the line
"#STATIC = -ccopt '-static'"

Usage:
Reads the query from stdin and prints the answer on stdout.

When the input is satisfiable, prints "Satisfiable: + formula" on stderr.
The formula implies the conjunction of the two input formula.

Options:
-debug: print debug information
-check: check the interpolant.
-sat: only check for satisfiability: print "(un)satisfiable" on stdout
-solver: choose which LA solver to use.

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

A number is an integer, floating point, or a ratio (number '/' number)
Warning: for the moment, "_1" is recognised as integer 1.

the authors: Dirk Beyer, Damien Zufferey, and Rupak Majumdar
