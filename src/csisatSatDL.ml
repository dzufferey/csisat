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
module PQueue =
  struct
    module Elt =
      struct
        type t = int * int
        let compare = compare
      end
    module PSet = Set.Make(Elt)

    type t = {
      mutable queue: PSet.t;
      mutable priorities: int IntMap.t;
    }

    let empty = {
      queue = PSet.empty;
      priorities = IntMap.empty
    }

    let get_min pq = PSet.min_elt pq.queue
    let get_priority pq idx = try IntMap.find idx pq.priorities with Not_found -> 0

    let add pq idx priority =
      let old_p = try IntMap.find idx pq.priorities with Not_found -> 0 in
      let q'  = if old_p < 0 then PSet.remove (old_p, idx) pq.queue else pq.queue in
      let q'' = if priority < 0 then PSet.add (priority, idx) q' else q' in
        pq.queue <- q'';
        pq.priorities <- IntMap.add idx priority pq.priorities

    let is_empty pq =
      PSet.is_empty pq.queue
      
  end
 
type potential_fct = (int * int) IntMap.t (*'satisfying' assignement, predecessor in the shortest path*)
type status = Unassigned
            | Assigned (* but not propagated *)
            | Propagated
            | Consequence (* a consequence of Propagated constraints *)
type kind = Equal | LessEq | LessStrict
type strictness = Strict | NonStrict

type t = {
  var_to_id: int ExprMap.t;
  mutable assignement: potential_fct;
  history: (predicate * potential_fct) Stack.t; (*TODO need something more ? labelling/consequences *)
  edges: (int * strictness * status) list array array; (*edges.(x).(y) = c is the edge x - y \leq c *)
}

let z_0 = Variable "__ZERO__"

(*
 natively support:
   x <= y + c and x < y + c
 in addition:
   x = y + c  -->  x <= y + c /\ y <= x - c
*)

(* returns 'v1 ? v2 + c as (?, v1, v2, c) TODO more general *)
let rec normalize_dl map pred =
  let (kind, e1, e2) = match pred with
    | Eq(Sum[Variable v1; Coeff (-1.0, Variable v2)], Constant c) -> (Equal, Variable v1, Sum [Variable v2; Constant c])
    | Lt(Sum[Variable v1; Coeff (-1.0, Variable v2)], Constant c) -> (LessStrict, Variable v1, Sum [Variable v2; Constant c])
    | Leq(Sum[Variable v1; Coeff (-1.0, Variable v2)], Constant c) -> (LessEq, Variable v1, Sum [Variable v2; Constant c])
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
    (kind, ExprMap.find v1 map, ExprMap.find v2 map, c2 - c1)

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
  (*initial assignement: 0 to everybody (is it right)*)
  let first_assign =
    List.fold_left
      (fun acc i -> IntMap.add i (0,-1) acc)
      IntMap.empty
      (Utils.range 0 n)
  in
  let edges = Array.make_matrix n n [] in
    (* fill edges *)
    PredSet.iter
      (fun p -> match normalize_dl var_to_id p with
        | (Equal, v1, v2, c) ->
          edges.(v1).(v2) <- ( c, NonStrict, Unassigned) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-c, NonStrict, Unassigned) :: edges.(v2).(v1)
          (*No negation for =*)
        | (LessEq, v1, v2, c) ->
          edges.(v1).(v2) <- ( c, NonStrict, Unassigned) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-c, Strict, Unassigned) :: edges.(v2).(v1) (*negation*)
        | (LessStrict, v1, v2, c) ->
          edges.(v1).(v2) <- ( c, Strict, Unassigned) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-c, NonStrict, Unassigned) :: edges.(v2).(v1) (*negation*)
      )
      (get_literal_set preds);
    {
      var_to_id= var_to_id;
      assignement = first_assign;
      history = history;
      edges = edges
    }

let active_constraint (_,_,status) = match status with Unassigned -> false | _ -> true in

let get_successors edges x =
  let succ = ref [] in
    Array.iteri
      (fun y lst ->
        let new_succ = List.filter active_constraint lst in
          succ := new_succ @ !succ
      )
      edges.(x);
    !succ

let eval potential_fct x =
  fst (ExprMap.find x potential_fct)

let is_sat t =
  valid t.assignement t.edges

let push t pred =
  let (kind, v1, v2, c) = normalize_dl t.var_to_id pred in
  (* check if it is already an active constraint *)
  let set_true v1 v2 c strictness =
    (*TODO set the constraint status (and weaker constraints as consequences)*)
    (*TODO propagate the consequences, store changes in stack, return satisfiability *)
    failwith "TODO"
  in
  let fct, changes = match kind with
    | Equal ->
      let v1_v2 = edges.(v1).(v2) in
      let v2_v1 = edges.(v2).(v1) in
        List.exists (fun (c',s,_) as cstr -> c = c' && s = NonStrict && active_constraint cstr) v1_v2 &&
        List.exists (fun (c',s,_) as cstr -> c = -1. *. c' && s = NonStrict && active_constraint cstr) v2_v1
    | LessEq ->
      let v1_v2 = edges.(v1).(v2) in
        List.exists (fun (c',s,_) as cstr -> c = c' && s = NonStrict && active_constraint cstr) v1_v2
    | LessStrict ->
      let v1_v2 = edges.(v1).(v2) in
        List.exists (fun (c',s,_) as cstr -> c = c' && s = Strict && active_constraint cstr) v1_v2
  in
    Stack.push t.history (pred, fct, changes);
    t.assignement <- fct;
    is_sat t

let pop () =
  (*TODO undo changes (stored in stack)*)
  failwith "TODO"

(*propagating equalities for NO*)
let propagations t exprs =
  (*TODO since there are all the predicates, is should be possible to do some T-propagation (for the sat solver)*)
  failwith "TODO"

(*info: but for the contradiction, cannot do much.*)
let unsat_core_with_info t = failwith "TODO"

let unsat_core t = let (p,_,_) = unsat_core_with_info t in p
