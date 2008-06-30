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

(** Abstract satsovler interface to allow different solvers*)

(**
 * @param with_proof should the satsolver keep the proof in memory
 *)
class virtual sat_solver (with_proof: bool) =
  object
    (** initialize the solver with given formula (in CNF) *)
    method virtual init: Ast.predicate -> unit
    (** add a clause (incremental use) *)
    method virtual add_clause: Ast.predicate -> unit
    (** is the system satisfiable ? *)
    method virtual solve: bool
    method virtual get_solution : Ast.predicate list
    method virtual get_proof: DpllProof.res_proof
  end
