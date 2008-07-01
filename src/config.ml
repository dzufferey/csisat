(*  CSIsat: interpolation procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

(** Parsing of argument + configuration variables *)

(** Syntax for I/O*)
type syntax_t = SyntaxFoci | SyntaxInfix

(**check the interpolant*)
let check = ref false
(** check the satisfiability, do not compute interpolant*)
let sat_only = ref false
(** round coefficient of the interpolant to get integers (!!limited precision)*)
let round = ref false
(** Syntax: foci or infix *)
let syntax = ref SyntaxFoci

let set_syntax str = match str with
  | "foci" -> syntax := SyntaxFoci
  | "infix" -> syntax := SyntaxInfix
  | _ -> failwith ("Unknown syntax: "^str)

let options = 
  [
    ("-debug", Arg.Unit Message.enable_debug,
      "Print debug information.");
    ("-check", Arg.Unit (fun () -> check := true),
      "Check the computed interpolant.");
    ("-sat", Arg.Unit (fun () -> sat_only := true),
      "Check for satisfiability only (no interplolation).\n Writes only \"satisfiable\" or \"unsatisfiable\" to stdout.");
    ("-LAsolver", Arg.String LIUtils.set_solver,
      "Choose the LA solver to use.\n Options: simplex, simplex_wo_presolve, interior (default: simplex).");
    ("-SATsolver", Arg.String SatPL.set_solver,
      "Choose the SAT solver to use.\n Options: csi_dpll, pico (default: csi_dpll). The PicoSAT integration is experimental.");
    ("-syntax", Arg.String set_syntax,
      "Choose the syntax to use.\n Options: foci, infix (default: foci).");
    ("-round", Arg.Unit (fun () -> round := true),
      "Try to round the coefficient to integer values. WARNING: still experimental")
  ]

let usage = (
  "CSIsat is an open-source interpolating decision procedure for LA+EUF.\n"^
  "Version: REV, DATE.\n\n"^
  "Reads the query from stdin and writes the answer to stdout.\n\n"^
  "If the input formula is satisfiable,\n CSIsat writes \"Satisfiable: <formula>\" on stderr.\n"^
  "'formula' implies the conjunction of the two input formula.\n"^
  "Otherwise it writes an interpolant to stdout.\n"
)

let _ = Arg.parse options (fun _ -> ()) usage
