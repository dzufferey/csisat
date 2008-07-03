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

(** Abstract satsovler interface to allow different solvers*)

module Ast       = CsisatAst
module DpllProof = CsisatDpllProof

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
