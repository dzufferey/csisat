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

(* fin an elegant way of getting ride of the strict constraints.
 * see: A Schrijver, Theory of Linear and Integer Programming, John Wiley and Sons, NY, 1987
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

    let get_min pq =
      (*Message.print Message.Debug (lazy("SatDL, PQueue: get_min"));*)
      PSet.min_elt pq.queue (*this raise Not_found if the set is empty*)

    let get_priority pq idx =
      (*Message.print Message.Debug (lazy("SatDL, PQueue: get_priority of " ^ (string_of_int idx)));*)
      try IntMap.find idx pq.priorities with Not_found -> pq.cutoff

    let add pq idx priority =
      (*Message.print Message.Debug (lazy("SatDL, PQueue: add "^(string_of_int idx)^" -> " ^ (string_of_float priority)));*)
      let old_p = try IntMap.find idx pq.priorities with Not_found -> pq.cutoff in
      let q'  = if old_p < pq.cutoff then PSet.remove (old_p, idx) pq.queue else pq.queue in
      let q'' = if priority < pq.cutoff then PSet.add (priority, idx) q' else q' in
        pq.queue <- q'';
        pq.priorities <- IntMap.add idx priority pq.priorities

    let remove pq idx =
      (*Message.print Message.Debug (lazy("SatDL, PQueue: remove " ^ (string_of_int idx)));*)
      try pq.queue <- PSet.remove (IntMap.find idx pq.priorities, idx) pq.queue
      with Not_found -> ();
      pq.priorities <- IntMap.remove idx pq.priorities

    let is_empty pq =
      (*Message.print Message.Debug (lazy("SatDL, PQueue: is_empty"));*)
      PSet.is_empty pq.queue
      
  end
 
type potential_fct = float array (*'-satisfying' assignment*)
type status = Unassigned
            | Assigned (* but not propagated *)
            | Consequence of predicate list (* a consequence of an Assigned constraints *)
type kind = Equal | LessEq | LessStrict
type strictness = Strict | NonStrict
type domain = Integer | Real
type edge_content = float * strictness * status * predicate
type edge = int * int * edge_content
type sat = Sat | UnSat of predicate * predicate list (* contradiction, predicate (given + T deduction) that are required to derive Not contradiction *)

type t = {
  domain: domain;
  var_to_id: int StringMap.t;
  id_to_expr: expression IntMap.t;
  mutable status: sat;
  mutable assignment: potential_fct;
  history: (predicate * potential_fct * (edge list)) Stack.t;
  edges: edge_content list array array; (*edges.(x).(y) = c is the edge x - y \leq c *)
}

let _z_0 = "__ZERO__"
let z_0 = Variable _z_0
let z_0_c = Constant 0.0

let copy t = 
  { domain = t.domain;
    var_to_id = t.var_to_id;
    id_to_expr = t.id_to_expr;
    status = t.status;
    assignment = t.assignment;
    history = Stack.copy t.history;
    edges = Array.map Array.copy t.edges
  }

let to_string t =
  let buffer = Buffer.create 1000 in
  let add = Buffer.add_string buffer in
    add ("DL solver over "^(if t.domain = Real then "R" else "Z")^" :\n");
    add "  variables: ";
    StringMap.iter (fun k v -> add (k^"("^(string_of_int v)^"),")) t.var_to_id;
    add "\n";
    begin
      match t.status with
      | Sat ->
        begin
          add "  status: sat\n";
          add "  assignment: sat\n";
          Array.iteri
            (fun i v ->
              add ((print_expr (IntMap.find i t.id_to_expr))^"="^(string_of_float (v -. t.assignment.(0)))^",")
            )
            t.assignment;
          add "\n";
        end
      | UnSat (ctr, core) ->
        begin
          add "  status: unsat\n";
          add ("    contradiction: "^(print_pred ctr)^"\n");
          add ("    reason: "^(String.concat ", " (List.map print_pred core))^"\n")
        end
    end;
    add "  constraints:  ";
    Array.iteri
      (fun x row ->
        Array.iteri
          (fun y lst ->
            let xs = print_expr (IntMap.find x t.id_to_expr) in
            let ys = print_expr (IntMap.find y t.id_to_expr) in
            let print (c,str,status,pred) = match status with
              | Unassigned -> ()
              | Assigned -> add ("(Given)"^xs^" - "^ys^" <="^(string_of_float c)^", ")
              | Consequence _ -> add ("(Conseq.)"^xs^" - "^ys^" <="^(string_of_float c)^", ")
            in
              List.iter print lst
          )
          row
      )
      t.edges;
    add "\n";
    Buffer.contents buffer

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
  let id1 = StringMap.find v1 map in
  let id2 = StringMap.find v2 map in
    adapt_domain domain (kind, id1, id2, c2 -. c1)

(*assume purified formula*)
let create domain preds =
  Message.print Message.Debug (lazy("SatDL: creating solver with " ^ (print_pred (And preds))));
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
      (1, StringMap.add _z_0 0 StringMap.empty, IntMap.add 0 z_0_c IntMap.empty)
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
          edges.(v1).(v2) <- (  c, NonStrict, Unassigned, p) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-.c, NonStrict, Unassigned, p) :: edges.(v2).(v1)
          (*No negation for =*)
        | (LessEq, v1, v2, c) ->
          edges.(v1).(v2) <- (  c, NonStrict, Unassigned, p) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-.c, Strict, Unassigned, normalize_only (Not p)) :: edges.(v2).(v1) (*negation*)
        | (LessStrict, v1, v2, c) ->
          edges.(v1).(v2) <- (  c, Strict, Unassigned, p) :: edges.(v1).(v2);
          edges.(v2).(v1) <- (-.c, NonStrict, Unassigned, normalize_only (Not p)) :: edges.(v2).(v1) (*negation*)
      )
      (get_literal_set (And preds));
    (* z_0 = 0 ? *)
    {
      domain = domain;
      var_to_id = var_to_id;
      id_to_expr = id_to_expr;
      status = Sat;
      assignment = first_assign;
      history = history;
      edges = edges
    }

let active_constraint (_,_,status,_) = match status with Unassigned -> false | _ -> true

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

let is_sat t = match t.status with Sat -> true | _ -> false

(*single source shortest path (default = dijkstra) (returns all the shortest path in pred)*)
let sssp size successors source =
  Message.print Message.Debug (lazy("SatDL: sssp from " ^ (string_of_int source)));
  let dist = Array.make size max_float in
  let pred = Array.make size (-1) in
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
                  pred.(idx') <- idx;
                  PQueue.add pq idx' d'
                end
              (*
              else if d' < dist.(idx') then
                begin
                  pred.(idx') <- idx :: pred.(idx');
                end
              *)

          )
          (successors idx)
    done;
    (dist, pred)

let strongest lst =
  (* TODO if strict && domain = Real then put some small k *)
  let is_stronger (d1, _, _, _) d2 = min d1 d2 in
  let dist (d, _, _, _) = d in
    List.fold_left
      (fun acc x -> match acc with
        | Some y -> Some (is_stronger x y)
        | None -> Some (dist x)
      )
      None
      (List.filter active_constraint lst)

let rec path_from_to pred source target =
  Message.print Message.Debug (lazy("SatDL: path from '" ^ (string_of_int source) ^ "' to '" ^ (string_of_int target)^"'"));
  if pred.(target) <> -1
  then target :: (path_from_to pred source (pred.(target)))
  else [source]
        
let rec path_to_pairs lst = match lst with
  | x :: y :: xs -> (x,y) :: path_to_pairs (y::xs)
  | _ -> []

let strongest_for_pair t (x,y) =
  let lst = List.filter active_constraint t.edges.(x).(y) in
  let (_,_,_,p) =
    List.fold_left
      (fun ((c,_,_,_) as c1) ((c',_,_,_) as c2) -> if c' < c then c2 else c1)
      (List.hd lst)
      (List.tl lst)
  in
    Message.print Message.Debug (lazy("SatDL: strongest_for_pair '" ^ (string_of_int x) ^ "' - '" ^ (string_of_int y)^"' is "^(print_pred p)));
    p

(*build the successors function for sssp using lazy elements*)
let lazy_successors t =
  let size = Array.length t.assignment in
  let successors_lists =
    Array.init
      size
      (fun idx ->
        lazy (
          snd (Array.fold_left
            (fun (idx', acc) lst ->
              ( idx' + 1,
                Utils.maybe
                  (* use assign to speed-up the process (Johnson algorithm):
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
    (fun x -> Lazy.force successors_lists.(x))

(*build the predecessor function for sssp using lazy elements*)
let lazy_predecessors t =
  let size = Array.length t.assignment in
  let preds_lists =
    Array.init
      size
      (fun idx ->
        lazy (
          snd (Array.fold_left
            (fun (idx', acc) lst ->
              ( idx' + 1,
                Utils.maybe
                  (* use assign to speed-up the process (Johnson algorithm):
                   * new weight are for x -c-> y is pi(x) + c - pi(y) *)
                  (fun x -> ((* -1. *. *) (t.assignment.(idx) +. x -. t.assignment.(idx')), idx')::acc) (*keep the edges positive ??*)
                  (lazy acc)
                  (strongest lst.(idx))
              )
            )
            (0, [])
            (t.edges))
        )
      )
  in
    (fun x -> Lazy.force preds_lists.(x))

(*propagating equalities for NO*)
let propagations t shared =
  Message.print Message.Debug (lazy("SatDL: propagations on " ^ (String.concat "," (List.map print_expr shared))));
  (* Assume the equalities are given at the beginning, just need to check if they are marked as Consequence
   * which means no sssp. *)
  (*look at the stack, get the changes from the last assignments *)
  if Stack.is_empty t.history then []
  else
    begin
      let (_, _, old_edges) = Stack.top t.history in
      let relevent_changes = (* pairs of a,b such that a <= b *)
        Utils.map_filter
          (fun (a, b, (c, _, _, _)) ->
            let a' = IntMap.find a t.id_to_expr in
            let b' = IntMap.find b t.id_to_expr in
              if c = 0.0 && List.mem a' shared && List.mem b' shared then Some (a, b) else None
          )
          old_edges
      in
      (*check that b <= a holds *)
      let check_entailed b a =
        let active_lst = List.filter active_constraint t.edges.(b).(a) in
        let equal_lst = List.filter (fun (c,_,_,_) -> c = 0.0) active_lst in
          equal_lst <> []
      in
      let equals = List.filter (fun (a,b) -> check_entailed b a) relevent_changes in
      let equalities =
        List.map
          (fun (a,b) -> order_eq (Eq (IntMap.find a t.id_to_expr, IntMap.find b t.id_to_expr)))
          equals
      in
        PredSet.elements (List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty equalities)
    end

let t_propagations t (x, y, c) pred =
  Message.print Message.Debug (lazy("SatDL: t_propagations after " ^ (print_pred pred)));
  (*only 2 sssp: when x -c-> y is added, only compute sssp from y and to x (reverse) *)
  let size = Array.length t.assignment in
  let successors = lazy_successors t in
  let predecessors = lazy_predecessors t in
  let shortest_x, pred_x = sssp size predecessors x in
  let shortest_y, pred_y = sssp size successors y in
  (*test for each unassigned constraints test*)
  let changed = ref [] in
    Array.iteri
      (fun i row ->
        Array.iteri
          (fun j lst ->
            let modif = ref false in
            let lst' =
              List.map
                (fun ((d, strict, status, p) as cstr) ->
                  if status = Unassigned && strict = Strict && shortest_x.(i) +. c +. shortest_y.(j) <= d then
                    begin
                      (*x -> i, j -> y, pred*)
                      let x_to_i = List.map (strongest_for_pair t) (path_to_pairs (List.rev (path_from_to pred_x x i))) in
                      let j_to_y = List.map (strongest_for_pair t) (path_to_pairs (path_from_to pred_y y j)) in
                      (*TODO check that path implies the constraint *)
                      let path = pred :: (x_to_i @ j_to_y) in
                        changed := (i, j, cstr) :: !changed;
                        (d, strict, Consequence path, p)
                    end
                  else
                     cstr
                )
                lst
            in
              if !modif then t.edges.(i).(j) <- lst'
          )
          row)
      t.edges;
    !changed

(*undo changes (stored in stack)*)
let pop t =
  Message.print Message.Debug (lazy("SatDL: pop"));
  let (_, assign, changes) = Stack.pop t.history in 
    t.assignment <- assign;
    List.iter
      (fun (v1, v2, (c, strict, status, p)) ->
        let current = t.edges.(v1).(v2) in
        let old =
          List.map
            (fun (c', strict', status', p') -> if c = c' && strict = strict' && p = p' then (c, strict, status, p) else (c', strict', status', p') )
            current
        in
          t.edges.(v1).(v2) <- old
      )
      changes;
    t.status <- Sat

(** Assume only push on a sat system *)
let push t pred =
  Message.print Message.Debug (lazy("SatDL: pushing " ^ (print_pred pred)));
  let (kind, v1, v2, c) = normalize_dl t.domain t.var_to_id pred in
  let set_true old_assign v1 v2 c strictness =
    Message.print Message.Debug (lazy("SatDL: set_true '" ^ (string_of_int v1) ^ "' - '" ^ (string_of_int v2) ^ "' <= " ^(string_of_float c)));
    (* check if it is already an active constraint *)
    let already =
      List.exists
        (fun ((_,_,_,p) as cstr) -> p = pred && active_constraint cstr)
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
              (fun (acc_c, acc_e) ((c', strictness', status, p) as cstr) ->
                if p = pred then
                  begin
                    let cstr' = (c', strictness', Assigned, p) in
                      ((v1, v2, cstr) :: acc_c, cstr' :: acc_e)
                  end
                else if status = Unassigned && (c < c' || (c = c' && (strictness = Strict || strictness' <> Strict))) then
                  begin
                    let cstr' = (c', strictness', Consequence [pred], p) in
                      ((v1, v2, cstr) :: acc_c, cstr' :: acc_e)
                  end
                else (acc_c, cstr :: acc_e)
              )
              ([], [])
              t.edges.(v1).(v2)
          in
            t.edges.(v1).(v2) <- new_edges;
            PQueue.add pq v2 (pi v1 +. c -. pi v2);
            while not (PQueue.is_empty pq) && PQueue.get_priority pq v1 = 0.0 do
              let (gamma_s, s) = PQueue.get_min pq in
                new_assign.(s) <- pi s +. gamma_s;
                PQueue.add pq s 0.0;
                List.iter
                  (fun (t,(c,strict,status,_)) ->
                    (* TODO if strict && domain = Real then put some small k *)
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
  let process_pred () = match kind with
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
  let sat, fct, changes = process_pred () in
  (*TODO check that the strict constraint are OK (and do the propagation) *)
  let old_assign = t.assignment in
    t.assignment <- fct;
    (* Do the propagation *)
    let changes' =
      if sat then
        match kind with
        | Equal -> (t_propagations t (v1, v2, c) pred) @ (t_propagations t (v2, v1, -1. *.c) pred)
        | _ -> t_propagations t (v1, v2, c) pred
      else []
    in
      (* store stuff on the stack *)
      Stack.push (pred, old_assign, changes @ changes') t.history;
      (* if unsat then find a small explanation *)
      if not sat then
        begin
          (* if there is a contradiction when adding x -c-> y then
           * there must be an negative cycle that goes though the x -c-> y edge.
           * We need to find that cycle.
           * let x -c'-> y the new edge where c has be modified according to the old assigment.
           * c' must be the only negative edge in the reweighted graph.
           * we must find a path from y to x, such that the weight of that path is strictly less than c'. *)
          (* restore previous graph*)
          pop t;
          (* get the shortest path from y to x *)
          let successors = lazy_successors t in
          let size = Array.length t.assignment in
          let shortest_y, pred_y = sssp size successors v2 in
          let path = List.rev (path_from_to pred_y v2 v1) in
          let y_to_x = List.map (strongest_for_pair t) (path_to_pairs path) in
          (*redo the changes (but no propagation)*)
          let sat, fct, changes = process_pred () in
          let old_assign = t.assignment in
            (* check that the distance y to x is less then x to y. *)
            (*
            Message.print Message.Debug (lazy("SatDL: path from "^(string_of_int v2)^" to "^(string_of_int v1)^" is " ^ (String.concat "-" (List.map string_of_int path))));
            Message.print Message.Debug (lazy("SatDL: shortest_y "^(String.concat ", " (List.map (fun (i,d) -> (string_of_int i)^"->"^(string_of_float d)) (Array.to_list (Array.mapi (fun i x -> (i,x)) shortest_y)) ))));
            Message.print Message.Debug (lazy("SatDL: assignment "^(String.concat ", " (List.map (fun (i,d) -> (string_of_int i)^"->"^(string_of_float d)) (Array.to_list (Array.mapi (fun i x -> (i,x)) old_assign)) ))));
            Message.print Message.Debug (lazy("SatDL: c = "^(string_of_float c)));
            *)
            assert(old_assign.(v2) +. shortest_y.(v1) -. old_assign.(v1) +. c < 0.0);
            t.assignment <- fct;
            Stack.push (pred, old_assign, changes) t.history;
            t.status <- UnSat (pred, y_to_x)
        end;
      sat

let rec get_given t p =
  let (k, v1, v2, c) = normalize_dl t.domain t.var_to_id p in
  let process_edge (c, strict, status, p) = 
    match status with
    | Unassigned -> failwith "SatDL, unsat_core_with_info: Unassigned"
    | Assigned -> (PredSet.empty, PredSet.singleton p)
    | Consequence antedecents ->
      begin
        let d, g = get_given_lst t antedecents in
        let d' = PredSet.add p d in
          (d', g)
      end
  in
  let edges = match k with
    | Equal ->
      [ List.find (fun (_,_,_,p') -> p = p' ) (t.edges.(v1).(v2)) ;
        List.find (fun (_,_,_,p') -> p = p' ) (t.edges.(v2).(v1)) ]
    | _ -> [List.find (fun (_,_,_,p') -> p = p' ) (t.edges.(v1).(v2))]
  in
  let processed_edges = List.map process_edge edges in
    List.fold_left
      (fun (a1, a2) (b1, b2) -> (PredSet.union a1 b1, PredSet.union a2 b2))
      (PredSet.empty, PredSet.empty)
      processed_edges

and get_given_lst t lst =
  List.fold_left
    (fun (acc1, acc2) p ->
      let d, g = get_given t p in
        (PredSet.union acc1 d, PredSet.union acc2 g)
      )
    (PredSet.empty, PredSet.empty)
    lst

(* order the deductions by looking into the stack *)
let order_deductions t set =
  let ordered = ref [] in
  let inspect_edge (_,_,(_,_,status,pred)) =
    if status = Unassigned && PredSet.mem pred set then
      ordered := pred :: !ordered
  in
  let inspect (_, _, lst) =
    List.iter inspect_edge lst
  in
  (*when there are equalities, only keep the last*)
  let rec eq_both_direction acc lst = match lst with
    | ((Eq (e1,e2)) as x)::xs ->
      begin
        let (ys, seen) = eq_both_direction (PredSet.add x acc) xs in
        let zs =
          if PredSet.mem x seen
          then (assert(not (PredSet.mem x acc)); x::ys)
          else ys
        in
          (zs, PredSet.add x seen)
      end
    | x::xs ->
      begin
        let (ys, seen) = eq_both_direction acc xs in
          (x::ys, seen)
      end
    | [] -> ([], PredSet.empty)
  in
    Stack.iter inspect t.history;
    let single, _ = eq_both_direction PredSet.empty !ordered in
    assert(List.length single = PredSet.cardinal set);
    single

let justify t pred =
  let deductions, given = get_given t pred in
  let odeductions = order_deductions t deductions in
  let contradiction = normalize (Not pred) in
    (And(contradiction :: (PredSet.elements given)), contradiction, DL, List.map (fun x -> (x,DL)) odeductions)

(*info: but for the contradiction, cannot do much.*)
let unsat_core_with_info t =
  match t.status with
  | Sat -> failwith "SatDL: unsat_core_with_info on a SAT system"
  | UnSat (pred, preds) ->
    begin
        let deductions, given = get_given_lst t preds in
        let odeductions = order_deductions t deductions in
          (And(pred :: (PredSet.elements given)), pred, DL, List.map (fun x -> (x,DL)) odeductions)
    end

let unsat_core t = let (p,_,_,_) = unsat_core_with_info t in p
