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
open   CsisatUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module IntMap  = CsisatUtils.IntMap
module Matrix  = CsisatMatrix
(**/**)

(*TODO 
 * For the interpolation, projecting the path on common variable do the job (see MathSat)
 * a proof of unsat is a shortest path that leads to a contradiction.
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
        type t = float * int
        let compare = compare
      end
    module PSet = Set.Make(Elt)

    type t = {
      cutoff : float;
      mutable queue: PSet.t;
      mutable priorities: float IntMap.t;
    }

    let empty cutoff = {
      cutoff = cutoff;
      queue = PSet.empty;
      priorities = IntMap.empty
    }

    let get_min pq = PSet.min_elt pq.queue
    let get_priority pq idx = try IntMap.find idx pq.priorities with Not_found -> pq.cutoff

    let add pq idx priority =
      let old_p = try IntMap.find idx pq.priorities with Not_found -> pq.cutoff in
      let q'  = if old_p < pq.cutoff then PSet.remove (old_p, idx) pq.queue else pq.queue in
      let q'' = if priority < pq.cutoff then PSet.add (priority, idx) q' else q' in
        pq.queue <- q'';
        pq.priorities <- IntMap.add idx priority pq.priorities

    let remove pq idx =
      try pq.queue <- PSet.remove (IntMap.find idx pq.priorities, idx) pq.queue
      with Not_found -> ();
      pq.priorities <- IntMap.remove idx pq.priorities

    let is_empty pq =
      PSet.is_empty pq.queue
      
  end
 
type potential_fct = float array (*'-satisfying' assignment*)
type status = Unassigned
            | Assigned (* but not propagated *)
            | Propagated
            | Consequence (* a consequence of Propagated constraints *)
type kind = Equal | LessEq | LessStrict
type strictness = Strict | NonStrict
type domain = Integer | Real
type edge_content = float * strictness * status
type edge = int * int * edge_content

type t = {
  domain: domain;
  var_to_id: int StringMap.t;
  id_to_expr: expression IntMap.t;
  mutable assignment: potential_fct;
  history: (predicate * potential_fct * (edge list)) Stack.t;
  edges: edge_content list array array; (*edges.(x).(y) = c is the edge x - y \leq c *)
}

let _z_0 = "__ZERO__"
let z_0 = Variable _z_0

(*TODO if use integers then no need for strict constraint.*)
(*
 natively support:
   x <= y + c and x < y + c
 in addition:
   x = y + c  -->  x <= y + c /\ y <= x - c
*)

let adapt_domain domain (kind, v1, v2, c) = match domain with
  | Integer when kind = LessStrict -> (LessEq, v1, v2, c -. 1.0)
  | _ -> (kind, v1, v2, c)

(* returns 'v1 ? v2 + c as (?, v1, v2, c) TODO more general *)
let rec normalize_dl domain map pred =
  let (kind, e1, e2) = match pred with
    | Eq(Sum[Variable v1; Coeff (-1.0, Variable v2)], Constant c) -> (Equal, Variable v1, Sum [Variable v2; Constant c])
    | Lt(Sum[Variable v1; Coeff (-1.0, Variable v2)], Constant c) -> (LessStrict, Variable v1, Sum [Variable v2; Constant c])
    | Leq(Sum[Variable v1; Coeff (-1.0, Variable v2)], Constant c) -> (LessEq, Variable v1, Sum [Variable v2; Constant c])
    | Eq(e1, e2) -> (Equal, e1, e2)
    | Lt(e1, e2) -> (LessStrict, e1, e2)
    | Leq(e1, e2) -> (LessEq, e1, e2)
    | err -> failwith ("SatDL expected DL predicate: "^(print_pred err))
  in
  let decompose_expr e = match e with
    | Variable x -> (x, 0.0)
    | Constant c -> (_z_0, c)
    | Sum [Variable x; Constant c] | Sum [Constant c; Variable x] -> (x, c)
    | err -> failwith ("SatDL, expected DL expression: "^(print_expr err))
  in
  let (v1,c1) = decompose_expr e1 in
  let (v2,c2) = decompose_expr e2 in
    adapt_domain domain (kind, StringMap.find v1 map, StringMap.find v2 map, c2 -. c1)

(*assume purified formula*)
let create domain preds =
  let vars = get_var (And preds) in
  let vars =
    List.map
      (fun x -> match x with
        | Variable v -> v
        | _ -> failwith "SatDL: get_vars returned smth else")
      vars
  in
  let (n, var_to_id, id_to_expr) = (*n is #vars + 1*)
    List.fold_left
      (fun (i, acc, acc2) v -> (i+1, StringMap.add v i acc, IntMap.add i (Variable v) acc2))
      (1, StringMap.add _z_0 0 StringMap.empty, IntMap.add 0 z_0 IntMap.empty)
      vars
  in
  let history = Stack.create () in
  (*initial assignment: 0 to everybody (is it right)*)
  let first_assign = Array.make n 0.0 in
  let edges = Array.make_matrix n n [] in
    (* fill edges *)
    PredSet.iter
      (fun p -> match normalize_dl domain var_to_id p with
        | (Equal, v1, v2, c) ->
          edges.(v1).(v2) <- (  c, NonStrict, Unassigned) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-.c, NonStrict, Unassigned) :: edges.(v2).(v1)
          (*No negation for =*)
        | (LessEq, v1, v2, c) ->
          edges.(v1).(v2) <- (  c, NonStrict, Unassigned) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-.c, Strict, Unassigned) :: edges.(v2).(v1) (*negation*)
        | (LessStrict, v1, v2, c) ->
          edges.(v1).(v2) <- (  c, Strict, Unassigned) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-.c, NonStrict, Unassigned) :: edges.(v2).(v1) (*negation*)
      )
      (get_literal_set (And preds));
    (* z_0 = 0 ? *)
    {
      domain = domain;
      var_to_id = var_to_id;
      id_to_expr = id_to_expr;
      assignment = first_assign;
      history = history;
      edges = edges
    }

let active_constraint (_,_,status) = match status with Unassigned -> false | _ -> true

let get_successors edges x =
  let succ = ref [] in
    Array.iteri
      (fun y lst ->
        let new_succ = List.filter active_constraint lst in
        let new_succ = List.map (fun c -> (y,c)) new_succ in
          succ := new_succ @ !succ
      )
      edges.(x);
    !succ

let eval potential_fct x = potential_fct.(x)

let is_sat t =
  failwith "TODO"

(** Assume only push on a sat system *)
let push t pred =
  let (kind, v1, v2, c) = normalize_dl t.domain t.var_to_id pred in
  let set_true old_assign v1 v2 c strictness =
    (* check if it is already an active constraint *)
    let already =
      List.exists
        (fun ((c',s,_) as cstr) -> c = c' && s = strictness && active_constraint cstr)
        t.edges.(v1).(v2)
    in
      if already then (true, t.assignment, [])
      else
        begin
          let new_assign = Array.copy old_assign in
          let pq = PQueue.empty 0.0 in
          let pi = eval old_assign in
          let pi' = eval new_assign in
          (* set the constraint status (and weaker constraints as consequences (trivial propagation))*)
          let changes, new_edges =
            List.fold_left
              (fun (acc_c, acc_e) ((c', strictness', status) as cstr) ->
                if c = c' && strictness = strictness' then
                  begin
                    let cstr' = (c', strictness', Assigned) in
                      ((v1, v2, cstr) :: acc_c, cstr' :: acc_e)
                  end
                else if status = Unassigned && (c < c' || (c = c' && strictness = Strict)) then
                  begin
                    let cstr' = (c', strictness', Consequence) in
                      ((v1, v2, cstr) :: acc_c, cstr' :: acc_e)
                  end
                else (acc_c, cstr :: acc_e)
              )
              ([], [])
              t.edges.(v1).(v2)
          in
            t.edges.(v1).(v2) <- new_edges;
            PQueue.add pq v2 (pi v1 +. c -. pi v2);
            while fst (PQueue.get_min pq) < 0.0 && PQueue.get_priority pq v1 = 0.0 do
              let (gamma_s, s) = PQueue.get_min pq in
                new_assign.(s) <- pi s +. gamma_s;
                PQueue.add pq s 0.0;
                List.iter
                  (fun (t,(c,strict,status)) ->
                    if status <> Unassigned && pi t = pi' t then
                      let gamma' = pi' s +. c -. pi t in
                        if gamma' < (PQueue.get_priority pq t) then
                          PQueue.add pq t gamma'
                  )
                  (get_successors t.edges s)
            done;
              if PQueue.get_priority pq v1 = 0.0
              then (true, new_assign, changes)
              else (false, new_assign, changes)
        end
  in
  let sat, fct, changes = match kind with
    | Equal ->
      begin
        let (sat, fct, changes) = set_true t.assignment v1 v2 c NonStrict in
          if sat then
            let (sat', fct', changes') = set_true fct v2 v1 (-1. *. c) NonStrict in
              (sat', fct', changes' @ changes)
          else
            (sat, fct, changes)
      end
    | LessEq -> set_true t.assignment v1 v2 c NonStrict
    | LessStrict -> set_true t.assignment v1 v2 c Strict
  in
    (*TODO check that the strict constraint are OK (and do the propagation) *)
    Stack.push (pred, t.assignment, changes) t.history;
    t.assignment <- fct;
    sat

(*undo changes (stored in stack)*)
let pop t =
  let (_, assign, changes) = Stack.pop t.history in 
    t.assignment <- assign;
    List.iter
      (fun (v1, v2, (c, strict, status)) ->
        let current = t.edges.(v1).(v2) in
        let old =
          List.map
            (fun (c', strict', status') -> if c = c' && strict = strict' then (c, strict, status) else (c', strict', status') )
            current
        in
          t.edges.(v1).(v2) <- old
      )
      changes

(*single source shortest path (default = dijkstra) (returns all the shortest path in pred)*)
let sssp size successors source =
  let dist = Array.make size max_float in
  let pred = Array.make size [] in
  let pq = PQueue.empty max_float in
    PQueue.add pq source 0.0 ;
    dist.(source) <- 0.0;
    while not (PQueue.is_empty pq) do
      let (d, idx) = PQueue.get_min pq in
        PQueue.remove pq idx;
        List.iter
          (fun (c, idx') ->
            let d' = d +. c in
              if d' < dist.(idx') then
                begin
                  dist.(idx') <- d';
                  pred.(idx') <- [idx];
                  PQueue.add pq idx' d'
                end
              else if d' = dist.(idx') then
                begin
                  pred.(idx') <- idx :: pred.(idx');
                end

          )
          (successors idx)
    done;
    (dist, pred)
  

(*propagating equalities for NO*)
let propagations t exprs =
  (*TODO double shortest path forward/backward
   * if need to propagate constraint, one call per unassigned constraint
   * to test for equality: |var| calls at most (assignment different should be a sufficient condition to reject)
   *)
  let size = Array.length t.assignment in
  let strongest lst =
    let is_stronger (d1, _, _) d2 = min d1 d2 in
    let dist (d, _, _) = d in
      List.fold_left
        (fun acc x -> match acc with
          | Some y -> Some (is_stronger x y)
          | None -> Some (dist x)
        )
        None
        (List.filter active_constraint lst)
  in
  (*build the successors function for sssp using lazy elements*)
  let successors_lists =
    Array.init
      size
      (fun idx ->
        lazy (
          snd (Array.fold_left
            (fun (idx', acc) lst ->
              ( idx' + 1,
                Utils.maybe
                  (* use assign to speed-up the process (like Johnson algorithm):
                   * new weight are for x -c-> y is pi(x) + c - pi(y) *)
                  (fun x -> (t.assignment.(idx) +. x -. t.assignment.(idx'), idx')::acc)
                  (lazy acc)
                  (strongest lst)
              )
            )
            (0, [])
            (t.edges.(idx)))
        )
      )
  in
  let successors x = Lazy.force successors_lists.(x) in
  let shortest_path =
    List.fold_left
      (fun acc exp ->
        match exp with
        | Variable var ->
          let idx = StringMap.find var t.var_to_id in
            IntMap.add idx (sssp size successors idx) acc
        | _ -> failwith "SatDL, propagations: expeted variables")
      IntMap.empty
      exprs 
  in
  (*TODO check if there is a contradiction *)
  let at_distance_0 =
    IntMap.fold
      (fun idx (dist, _) acc ->
        let zeros = ref [] in
          (*TODO check preds for contradiction*)
          Array.iteri (fun i x -> if x = 0.0 && i <> idx then zeros := i :: !zeros) dist;
          (List.map (fun x -> (idx, x) )!zeros) @ acc
      )
      shortest_path
      []
  in
  (*check which are equals (dist = 0 both direction) *)
  let implied_equalities = List.filter (fun (a,b) -> (a < b) && List.mem (b,a) at_distance_0) at_distance_0 in
    List.map (fun (a,b) -> order_eq (Eq (IntMap.find a t.id_to_expr, IntMap.find b t.id_to_expr)) ) implied_equalities

let t_propagations t =
  (*TODO double shortest path forward/backward
   * if need to propagate constraint, one call per unassigned constraint
   *)
  (*TODO store changes in stack*)
  (* similar to propagations for NO *)
  failwith "TODO"

(*info: but for the contradiction, cannot do much.*)
let unsat_core_with_info t = failwith "TODO"

let unsat_core t = let (p,_,_) = unsat_core_with_info t in p
