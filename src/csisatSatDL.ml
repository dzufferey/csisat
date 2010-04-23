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
  var_to_id: int ExprMap.t;
  mutable assignement: potential_fct;
  history: (predicate * potential_fct) Stack.t; (*TODO need something more ? labelling/consequences *)
  edges: (int * status) array array;
}

let z_0 = Variable "__ZERO__"

(*
 natively support:
   x <= y + c and x < y + c
 in addition:
   x = y + c  -->  x <= y + c /\ y <= x - c
*)

type kind = Equal | LessEq | LessStrict

(* returns 'v1 ? v2 + c as (?, v1, v2, c) *)
let normalize_dl pred =
  let (kind, e1, d2) = match pred with
    | Eq(e1, e2) -> (Equal, e1, e2)
    | Lt(e1, e2) -> (LessStrict, e1, e2)
    | Leq(e1, e2) -> (LessEq, e1, e2)
  in
  let decompose_expr e = match w with
    | Variable x -> (x, 0)
    | Constant c -> assert (Utils.is_integer c); (z_0, int_of_float c)
    | Sum[Variable x, Constant c] | Sum[Constant c, Variable x] ->
      assert (Global.is_off_assert() || Utils.is_integer c);
      (x, int_of_float c)
    | err -> failwith ("SatDL, expected DL expression: "^(print_expr err))
  in
  let (v1,c1) = decompose_expr e1 in
  let (v2,c2) = decompose_expr e2 in
    (kind, v1, v2, c2 - c1)

(*assume purified formula*)
let create preds =
  let vars = get_var (And preds) in
  let (n, var_to_id) = (*n is #vars + 1*)
    List.fold_left
      (fun (i, acc) v -> (i+1, ExprMap.add v i acc))
      (1, ExprMap.singleton z_0 0)
      vars
  in
  let history = Stack.create () in
  let edges = Array.make_matrix n n (0, Empty) in
    (*TODO fill edges *)
    (*TODO initial assignement *)
    failwith "TODO"

let push t pred = failwith "TODO"

let pop pred = failwith "TODO"

let is_sat t = failwith "TODO"

(*propagating equalities for NO*)
let propagations t exprs = failwith "TODO"

let unsat_core_with_info t = failwith "TODO"

let unsat_core t = let (p,_,_) = unsat_core_with_info t in p
