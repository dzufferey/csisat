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

let check = ref false
let sat_only = ref false

let options = 
  [
    ("-debug", Arg.Unit Message.enable_debug,
      "Print debugging informations");
    ("-check", Arg.Unit (fun () -> check := true),
      "check computed interpolant");
    ("-sat", Arg.Unit (fun () -> sat_only := true),
      "only check if the assignement is satisfiable or not (no interplolation), prints '(un)satisfiable' on stdout");
    ("-solver", Arg.String LIUtils.set_solver,
      "choose LA solver option: simplex, simplex_wo_presolve, interior. (default: simplex)")
  ]

let usage = (
  "CSIsat is an open source interpolation procedure \n\n"^
  "Reads the query from stdin and prints the answer on stdout.\n"^
  "When the input is satisfiable, prints \"Satisfiable: + formula\" on stderr.\n"^
  "The formula implies the conjunction of the two input formula.\n"
)

let _ = Arg.parse options (fun _ -> ()) usage
