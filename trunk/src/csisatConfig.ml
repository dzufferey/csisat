(*  CSIsat: interpolation procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *)

(** Parsing of argument + configuration variables *)

(** Syntax for I/O*)
type syntax_t = SyntaxFoci | SyntaxInfix | SyntaxUnk

(**check the interpolant*)
let check = ref false
(** check the satisfiability, do not compute interpolant*)
let sat_only = ref false
(** round coefficient of the interpolant to get integers (!!limited precision)*)
let round = ref false
(** x < y  ~>  x+1 <= y *)
let integer_heuristics = ref false
(** Syntax: foci or infix *)
let syntax = ref SyntaxUnk

let set_syntax str = match str with
  | "foci" -> syntax := SyntaxFoci
  | "infix" -> syntax := SyntaxInfix
  | _ -> failwith ("Unknown syntax: "^str)

let options = 
  [
    ("-debug", Arg.Unit CsisatMessage.enable_debug,
      "Print debug information.");
    ("-check", Arg.Unit (fun () -> check := true),
      "Check the computed interpolant.");
    ("-sat", Arg.Unit (fun () -> sat_only := true),
      "Check for satisfiability only (no interplolation).\n     Writes only \"satisfiable\" or \"unsatisfiable\" to stdout.");
    ("-LAsolver", Arg.String CsisatLIUtils.set_solver,
      "Choose the LA solver to use.\n    Options: simplex, simplex_wo_presolve, interior (default: simplex).");
    ("-SATsolver", Arg.String CsisatSatPL.set_solver,
      "Choose the SAT solver to use.\n    Options: csi_dpll, pico (default: csi_dpll). The PicoSAT integration is experimental.");
    ("-syntax", Arg.String set_syntax,
      "Choose the syntax to use.\n    Options: foci, infix (default: try foci first then infix if it fail).");
    ("-round", Arg.Unit (fun () -> round := true),
      "Try to round the coefficient to integer values. WARNING: still experimental.");
    ("-int", Arg.Unit (fun () -> integer_heuristics := true),
      "Apply heuristics to solve over integers. This is not sound, neither complete in general.")
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
