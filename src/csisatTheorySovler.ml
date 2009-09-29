(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *  Copyright (C) 2007-2008  The CSIsat team
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
 *
 *  For information about the CSIsat project,
 *  please visit the CSIsat web page at:
 *  http://www.cs.sfu.ca/~dbeyer/CSIsat/

 *)

(** Interface for stateful incremental theory solver. *)

(**/**)
module Ast       = CsisatAst
module AstUtil = CsisatAstUtil
module AstUtil = CsisatAstUtil
module PredSet = CsisatAstUtil.PredSet
(**/**)

module type TheorySolver =
  sig
    (** a mutable/stateful incremental theory solver *)
    type t

    (** Creates a new solver, initially without constraints.
     * @param list of all potential predicates (for T-propagation)
     *)
    val create: PredSet.t -> t

    (** Adds and test for satisfiability. *)
    val push: t -> Ast.predicate -> bool
    
    (** Removes the predicate on top of the stacks. *)
    val pop: t -> unit
    
    (** Returns a list of predicates equalities that are
     * entailed by the current stack (report only changes from last addition).
     *)
    val propagation: t -> Ast.predicate list
    
    (** Returns:
     *  -unsat_core
     *  -the theory which has a contradiction
     *  -list of deduced equalities + their respective theories. 
     *)
    val unsat_core_with_info: t -> (Ast.predicate * Ast.theory * (Ast.predicate * Ast.theory) list)

    (** Performs some conflict analysis and
     * returns an unsatisfiable conjuntion composed
     * of predicate from the current stack. *)
    val unsat_core: t -> Ast.predicate
    (* unsat_core t = let (p,_,_) = unsat_core_with_info t in p *)
  end
