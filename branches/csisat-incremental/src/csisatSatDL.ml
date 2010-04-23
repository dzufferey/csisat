(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
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
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)

(** Satisfiability for difference logic. *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatLIUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module Utils   = CsisatUtils
module IntMap  = CsisatUtils.IntMap
module Matrix  = CsisatMatrix
(**/**)

(*TODO 
 * the classical algorithm for DL is to use difference bound matrix (i.e. shortest path algorithms).
 * But we need to do it in an incremental way.
 * For the interpolation, projecting the path on common variable do the job (see MathSat)
 *
 * let's try to follow:
 * "fast and flexible difference constraints propagation for DPLL(T)"
 * by Scott Cotton and Oded Maler
 *)

(* TODO need something like a binary heap / fibbonaci heap / bordal queue
 * a binary heap should be sufficient to start.
 * In the mean time, it is possible o use a set of pairs (priority, id).
 *)
 
type potential_fct = (int * int) IntMap.t (*'satisfying' assignement, predecessor in the shortest path*)
type status = Unassigned
            | Assigned (* but not propagated *)
            | Propagated
            | Consequence (* a consequence of Propagated constraints *)
            | Empty

type t = {
  expre_to_id: int ExprMap.t;
  mutable assignement: potential_fct;
  history: (predicate * potential_fct) Stack.t; (*TODO need something more ? labelling/consequences *)
  edges: (int * status) array array;
}

let create preds = failwith "TODO"

let push t pred = failwith "TODO"

let pop pred = failwith "TODO"

let is_sat t = failwith "TODO"

(*propagating equalities for NO*)
let propagations t exprs = failwith "TODO"

let unsat_core_with_info t = failwith "TODO"

let unsat_core t = let (p,_,_) = unsat_core_with_info t in p
