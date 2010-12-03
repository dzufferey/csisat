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
module OrdSet  = CsisatOrdSet
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


(* 
 * divided into 2 parts:
 * ( i) basic solver only nonstrict, no equal, don't care oabout domain, ... 
 * (ii) layer to take care of ==, leq in Integer/Real domain, proof rewriting, ...
 *
 * Integer vs Real: find an elegant way of getting ride of the strict constraints (small epsilon).
 * see: A Schrijver, Theory of Linear and Integer Programming, John Wiley and Sons, NY, 1987
 *
 * build an actual proof of unsat using the given constraints ... 
 *)
    
module Diff =
  struct
    type t = int * int * float (* a - b <= c *)
    let compare = Pervasives.compare
    let to_string (x,y,c) = "'" ^ (string_of_int x) ^ "' - '" ^ (string_of_int y) ^ "' <= " ^ (string_of_float c)
    let a (a,_,_) = a
    let b (_,b,_) = b
    let c (_,_,c) = c
    let weaker (a,b,c) (a',b',c') = if a <> a' || b <> b' then failwith "Invalid Argument" else c >= c'
  end
module DiffSet = Set.Make(Diff)
module DiffMap = Map.Make(Diff)
 
module BasicSolver =
  struct
    
    module Proof =
      struct
        type t = Diff.t * Diff.t list
        
        let what prf = fst prf
        let path prf = snd prf
        let hd (_,prf) = Diff.a (List.hd prf)
        let last (_,prf) = Diff.b (List.nth prf (List.length prf -1))

        let compact_path prf =
          let a = Diff.a (List.hd prf) in
          let b = Diff.b (List.nth prf (List.length prf -1)) in
          let c = List.fold_left (fun acc diff -> acc +. (Diff.c diff)) 0.0 prf in
            (a,b,c)

        let create prf = (compact_path prf, prf)
        
        let strongest_consequence prf = compact_path (path prf)

        let well_formed (goal, prf) = 
          let a = List.tl (List.map Diff.a prf) in
          let b = List.rev (List.tl (List.rev (List.map Diff.b prf))) in
            (List.for_all2 (=) a b) && Diff.weaker goal (strongest_consequence (goal, prf))

        (*let to_string prf = "\\inferrule{ "^(String.concat " \\\\ " (List.map Diff.to_string (path prf)))^" }{ "^(Diff.to_string (what prf))^" }"*)
        let to_string (goal, lst) =
          (String.concat "," (List.map Diff.to_string lst)) ^ " ==> " ^ (Diff.to_string goal)

        let append prf1 prf2 =
          if (last prf1) <> (hd prf2)
          then failwith "Invalid Argument"
          else create ((path prf1) @ (path prf2))

        let order_path first last_one lst =
          Message.print Message.Debug (lazy("SatDL, Proof: order_path ("^(string_of_int first)^","^(string_of_int last_one)^") -> " ^ (String.concat "," (List.map Diff.to_string lst))));
          let rec build_path x acc lst =
            let (x,xs) = List.partition (fun d -> (Diff.a d) = x) lst in
              match x with
              | [d] -> build_path (Diff.b d) (d::acc) xs
              | [] -> assert(xs = []); List.rev acc
              | err -> failwith ("SatDL, Proof, order_path: multiple successors/not a simple path " ^ (String.concat "," (List.map Diff.to_string err)))
          in
          let path = build_path first [] lst in
          let proof = create path in
            assert(last_one = (last proof));
            proof

      end

    type diff_constraint = Diff.t
    type potential_fct = float array (*'-satisfying' assignment*)
    type status = Unassigned
                | Assigned
                | Consequence of Proof.t
    type edge_content = float * status
    type edge = int * int * edge_content
    type sat = Sat
             | UnSat of diff_constraint * Proof.t (* contradiction, proof that derives Not contradiction *)

    type t = {
      mutable status: sat;
      mutable assignment: potential_fct;
      history: (diff_constraint * potential_fct * (edge list)) Stack.t;
      edges: edge_content list array array; (*edges.(x).(y) = c is the edge x - y \leq c *)
    }

    let string_of_status s = match s with
      | Unassigned -> "Unassigned"
      | Assigned -> "Assigned"
      | Consequence prf -> "Consequence of " ^ (Proof.to_string prf)

    let to_string t =
      let buffer = Buffer.create 1000 in
      let add = Buffer.add_string buffer in
        add ("DL solver :\n");
        begin
          match t.status with
          | Sat ->
            begin
              add "  status: sat\n";
              add "  assignment: sat\n";
              Array.iteri
                (fun i v -> add ("'"^(string_of_int i)^"' = "^(string_of_float (v -. t.assignment.(0)))^","))
                t.assignment;
              add "\n";
            end
          | UnSat (ctr, core) ->
            begin
              add "  status: unsat\n";
              add ("    contradiction: "^(Diff.to_string ctr)^"\n");
              add ("    reason: "^(Proof.to_string core)^"\n")
            end
        end;
        add "  constraints:  ";
        Array.iteri
          (fun x row ->
            Array.iteri
              (fun y lst ->
                let print (c,status) = match status with
                  | Unassigned -> ()
                  | Assigned -> add ("(Given)"^(Diff.to_string (x,y,c))^", ")
                  | Consequence _ -> add ("(Conseq.)"^(Diff.to_string (x,y,c))^", ")
                in
                  List.iter print lst
              )
              row
          )
          t.edges;
        add "\n";
        Buffer.contents buffer

    (* WARNING diff_constraint should ideally contains the constraints and their negation ? (how to deal with Int vs Real) *)
    let create diff_constraints =
      Message.print Message.Debug (lazy("SatDL: creating solver with " ^ (String.concat "," (List.map Diff.to_string diff_constraints))));
      let n = (List.fold_left (fun acc (v1,v2,_) -> max acc (max v1 v2)) 0 diff_constraints) + 1 in
      let history = Stack.create () in
      (*initial assignment: 0 to everybody (is it right)*)
      let first_assign = Array.make n 0.0 in
      let edges = Array.make_matrix n n [] in
        (* fill edges *)
        List.iter
          (fun (v1,v2,c) -> edges.(v1).(v2) <- (c, Unassigned) :: edges.(v1).(v2) )
          diff_constraints;
        for i = 0 to n-1 do
          for j = 0 to n-1 do
            edges.(i).(j) <- OrdSet.remove_duplicates edges.(i).(j)
          done
        done;
        {
          status = Sat;
          assignment = first_assign;
          history = history;
          edges = edges
        }

    let active_constraint (_,status) = match status with Unassigned -> false | _ -> true

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
                Message.print Message.Debug (lazy("SatDL: "^(string_of_int idx)^" -("^(string_of_float c)^")-> "^(string_of_int idx')));
                let d' = d +. c in
                  if d' < dist.(idx') then
                    begin
                      dist.(idx') <- d';
                      pred.(idx') <- idx;
                      PQueue.add pq idx' d'
                    end
              )
              (successors idx)
        done;
        (dist, pred)

    let strongest lst =
      let is_stronger (d1, _) d2 = min d1 d2 in
      let dist (d, _) = d in
        List.fold_left
          (fun acc x -> match acc with
            | Some y -> Some (is_stronger x y)
            | None -> Some (dist x)
          )
          None
          (List.filter active_constraint lst)

    let rec path_from_to_rev pred source target =
      (*Message.print Message.Debug (lazy("SatDL: path from '" ^ (string_of_int source) ^ "' to '" ^ (string_of_int target)^"'"));*)
      if pred.(target) <> -1
      then target :: (path_from_to_rev pred source (pred.(target)))
      else [source]
    let rec path_from_to pred source target = List.rev (path_from_to_rev pred source target)
        
    let strongest_for_pair t (x,y) =
      let lst = List.filter active_constraint t.edges.(x).(y) in
      let (c,_) =
        List.fold_left
          (fun ((c,_) as c1) ((c',_) as c2) -> if c' < c then c2 else c1)
          (List.hd lst)
          (List.tl lst)
      in
        (*Message.print Message.Debug (lazy("SatDL: strongest_for_pair " ^ (Diff.to_string (x,y,c))));*)
        (x,y,c)

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
                      (*TODO is it th rigt thing to do ?? ''' vs ' ' *)
                      (fun x -> ((t.assignment.(idx') +. x -. t.assignment.(idx)), idx')::acc) (*keep the edges positive ??*)
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

    (* test if a predicate is entailed by the current model
     * this is for NO only and it assumes there are 'edges' between
     * the nodes in p.
     *)
    let entailed t (v1, v2, c) =
      let res =
        List.exists
          (fun ((c2,_) as cstr) -> c >= c2 && active_constraint cstr)
          t.edges.(v1).(v2)
      in
        Message.print Message.Debug (lazy("SatDL: entailed " ^ (Diff.to_string (v1,v2,c)) ^ " -> " ^ (string_of_bool res)));
        res
    
    let mk_proof t (a,b,c) =
      (* If the diff already exists in the edges the simple.
       * Otherwise, must go through the sssp computation like t_propagations. *)
      Message.print Message.Debug (lazy("SatDL: mk_proof " ^ (Diff.to_string (a,b,c))));
      let process_edge (c, status) = 
        match status with
        | Unassigned -> failwith "SatDL, make_proof: Unassigned"
        | Assigned -> Proof.create [(a,b,c)]
        | Consequence prf -> prf
      in
        try 
          let edges = List.find_all (fun (c',d) -> c' <= c && d <> Unassigned) (t.edges.(a).(b)) in
          let edge = if edges = [] then raise Not_found else List.hd edges in
            process_edge edge
        with Not_found ->
          begin
            Message.print Message.Debug (lazy("SatDL: mk_proof neither a consequence nor given"));
            failwith "TODO: stuff that are not there -> sssp ..."
          end

    let rec expand_proof t prf =
      let path = Proof.path prf in
      let full_proof = List.fold_left (fun prf diff -> Proof.append prf (mk_proof t diff)) (mk_proof t (List.hd path)) (List.tl path) in
        if prf = full_proof then prf else expand_proof t full_proof


    (*propagating equalities for NO*)
    let propagations t shared =
      (* Assume the equalities are given at the beginning, just need to check if they are marked as Consequence
       * which means no sssp. *)
      (*look at the stack, get the changes from the last assignments *)
      if Stack.is_empty t.history then []
      else
        begin
          (*TODO go further ?? *)
          let (_, _, old_edges) = Stack.top t.history in
          let relevent_changes = (* pairs of a,b such that a <= b *)
            Utils.map_filter
              (*TODO is it right not to check the status ?? *)
              (fun (a, b, (c, _)) ->
                  if c = 0.0 && List.mem a shared && List.mem b shared then Some (a, b) else None
              )
              old_edges
          in
          let equals = List.filter (fun (a,b) -> entailed t (b, a, 0.0)) relevent_changes in
            OrdSet.remove_duplicates equals
        end

    let t_propagations t (x, y, c) =
      Message.print Message.Debug (lazy("SatDL: t_propagations after " ^ (Diff.to_string (x,y,c))));
      Message.print Message.Debug (lazy("SatDL: "^(String.concat ", " (Array.to_list (Array.mapi (fun i v -> (string_of_int i)^" = "^(string_of_float v)) t.assignment)))));
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
            (*Message.print Message.Debug (lazy("SatDL: shortest_"^(string_of_int x)^".("^(string_of_int i)^") = " ^ (string_of_float shortest_x.(i))));*)
            Array.iteri
              (fun j lst ->
                (*Message.print Message.Debug (lazy("SatDL: shortest_"^(string_of_int y)^".("^(string_of_int j)^") = " ^ (string_of_float shortest_y.(j))));*)
                let lst' =
                  List.map
                    (fun ((d, status) as cstr) ->
                      let shortest_path = shortest_x.(i) +. c +. shortest_y.(j) in
                      let path_weight = shortest_path +. t.assignment.(x) -. t.assignment.(y) +. t.assignment.(j) -. t.assignment.(i) in
                        Message.print Message.Debug (lazy("SatDL: deduced " ^ (Diff.to_string (i,j,shortest_path)) ^ " --> "^ (Diff.to_string (i,j,path_weight))));
                        if status = Unassigned && path_weight <= d then
                          begin
                            (*x -> i, j -> y, pred*)
                            let mk_path lst = List.map (strongest_for_pair t) (path_to_edges lst) in 
                            (*Message.print Message.Debug (lazy("SatDL: x_to_i"));*)
                            let x_to_i = mk_path (path_from_to_rev pred_x x i) in
                            (*Message.print Message.Debug (lazy("SatDL: j_to_y"));*)
                            let j_to_y = mk_path (path_from_to pred_y y j) in
                            let raw_path = (x,y,c) :: (x_to_i @ j_to_y) in
                            let init_proof = Proof.order_path i j raw_path in
                            (*TODO make sure that all the edges in the path are given element, not consequences *)
                            let full_proof = expand_proof t init_proof in
                            let proof = ((i,j,d), Proof.path full_proof) in
                              assert (Proof.well_formed proof);
                              changed := (i, j, cstr) :: !changed;
                              Message.print Message.Debug (lazy("SatDL: Consequence " ^ (Diff.to_string (i,j,d) ^ " because " ^ (Proof.to_string proof))));
                              (d, Consequence proof)
                          end
                        else
                          cstr
                    )
                    lst
                in
                  t.edges.(i).(j) <- lst'
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
          (fun (v1, v2, (c, status)) ->
            let current = t.edges.(v1).(v2) in
            let old =
              List.map
                (fun (c', status') -> if c = c' then (c, status) else (c', status') )
                current
            in
              t.edges.(v1).(v2) <- old
          )
          changes;
        t.status <- Sat

    (** Assume only push on a sat system *)
    let push t (v1, v2, c) =
      Message.print Message.Debug (lazy("SatDL: pushing " ^ (Diff.to_string (v1,v2,c))));
      (* check if it is already an active constraint *)
      let already =
        List.exists
          (fun ((c2,_) as cstr) -> c = c2 && active_constraint cstr)
          t.edges.(v1).(v2)
      in
      (* preform the changes *)
      let process_pred () = 
        if already then (true, t.assignment, [])
        else
          begin
            Message.print Message.Debug (lazy("SatDL: new constraint "));
            let new_assign = Array.copy t.assignment in
            let pq = PQueue.empty 0.0 in
            let pi = eval t.assignment in
            let pi' = eval new_assign in
            (* set the constraint status (and weaker constraints as consequences (trivial propagation))*)
            let changes, new_edges =
              List.fold_left
                (fun (acc_c, acc_e) ((c', status) as cstr) ->
                  if c = c' then
                    begin
                      let cstr' = (c', Assigned) in
                        ((v1, v2, cstr) :: acc_c, cstr' :: acc_e)
                    end
                  else if status = Unassigned && c <= c' then
                    begin
                      let cstr' = (c', Consequence ((v1,v2,c'), [(v1,v2,c)])) in
                        Message.print Message.Debug (lazy("SatDL: direct consequence " ^ (Diff.to_string (v1,v2,c'))));
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
                    (fun (t,(c,status)) ->
                      if status <> Unassigned && pi t = pi' t then
                        let gamma' = pi' s +. c -. pi t in
                          if gamma' < (PQueue.get_priority pq t) then
                            PQueue.add pq t gamma'
                    )
                    (get_successors t.edges s)
              done;
              let v1_p = PQueue.get_priority pq v1 in
                Message.print Message.Debug (lazy("SatDL: priority of v1 = " ^ (string_of_float v1_p)));
                if v1_p >= 0.0
                then (true, new_assign, changes)
                else (false, new_assign, changes)
          end
      in
      let sat, fct, changes = process_pred () in
      let old_assign = t.assignment in
        t.assignment <- fct;
        (* Do the propagation *)
        let changes' =
          if sat then t_propagations t (v1, v2, c)
          else []
        in
          (* store stuff on the stack *)
          Stack.push ((v1, v2, c), old_assign, changes @ changes') t.history;
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
              let find_path v1 v2 c =
                let shortest_y, pred_y = sssp size successors v2 in
                let path = path_from_to pred_y v2 v1 in
                let y_to_x = List.map (strongest_for_pair t) (path_to_edges path) in
                  (* check that the distance y to x is less then x to y. *)
                  Message.print Message.Debug (lazy("SatDL: path from "^(string_of_int v2)^" to "^(string_of_int v1)^" is " ^ (String.concat "-" (List.map string_of_int path))));
                  Message.print Message.Debug (lazy("SatDL: shortest_y "^(String.concat ", " (List.map (fun (i,d) -> (string_of_int i)^"->"^(string_of_float d)) (Array.to_list (Array.mapi (fun i x -> (i,x)) shortest_y)) ))));
                  Message.print Message.Debug (lazy("SatDL: assignment "^(String.concat ", " (List.map (fun (i,d) -> (string_of_int i)^"->"^(string_of_float d)) (Array.to_list (Array.mapi (fun i x -> (i,x)) old_assign)) ))));
                  Message.print Message.Debug (lazy("SatDL: c = "^(string_of_float c)));
                  Message.print Message.Debug (lazy("SatDL: old_assign.(v1) +. shortest_y.(v1) -. old_assign.(v2) +. c = "^(string_of_float (old_assign.(v1) +. shortest_y.(v1) -. old_assign.(v2) +. c))));
                  if old_assign.(v1) +. shortest_y.(v1) -. old_assign.(v2) +. c < 0.0
                  then Some (y_to_x)
                  else None
              in
              let y_to_x = maybe (fun x -> x) (lazy (failwith "SatDL: find_path")) (find_path v1 v2 c) in
              let proof = expand_proof t (Proof.create y_to_x) in
              (*redo the changes (but no propagation)*)
              let sat, fct, changes = process_pred () in
              let old_assign = t.assignment in
                t.assignment <- fct;
                Stack.push ((v1,v2,c), old_assign, changes @ changes') t.history;
                t.status <- UnSat ((v1,v2,c), proof)
            end;
          Message.print Message.Debug (lazy("SatDL: after push -> " ^ (string_of_bool sat)));
          sat

    let get_given t (v1,v2,c) =
      Message.print Message.Debug (lazy("SatDL: get_given " ^ (Diff.to_string (v1,v2,c))));
      Message.print Message.Debug (lazy("SatDL, get_given: edges = " ^ (String.concat ", " (List.map (fun (a,b) -> "("^(string_of_float a)^","^(string_of_status b)^")") t.edges.(v1).(v2)))));
      let process_edge (c, status) = 
        match status with
        | Unassigned -> failwith "SatDL, get_given: Unassigned"
        | Assigned -> DiffSet.singleton (v1,v2,c)
        | Consequence prf -> List.fold_left (fun acc x -> DiffSet.add x acc) DiffSet.empty (Proof.path prf)
      in
      let edge = List.find (fun (c',_) -> c = c' ) (t.edges.(v1).(v2)) in
        process_edge edge

    let get_given_lst t lst =
      List.fold_left
        (fun acc p ->
          let g = get_given t p in
            DiffSet.union acc g
          )
        DiffSet.empty
        lst

    (*info: but for the contradiction, cannot do much.
     * returns proof => ~pred
     *)
    let unsat_core_with_info t =
      match t.status with
      | Sat -> failwith "SatDL: unsat_core_with_info on a SAT system"
      | UnSat (pred, proof) -> (pred, proof)

  end

module InterfaceLayer =
  struct
    type domain = Integer | Real
    type kind = Equal | LessEq | LessStrict
    
    let _z_0 = "__ZERO__"
    let z_0 = Variable _z_0
    let z_0_c = Constant 0.0
    (*TODO make sure epsilon is small enough w.r.t. the problem constants *)
    let epsilon = 1.e-5

    let adapt_domain domain (kind, v1, v2, c) = match (domain, kind) with
      | (Integer, LessStrict) -> (v1, v2, c -. 1.0)
      | (Real, LessStrict) -> (v1, v2, c -. epsilon)
      | (Integer, LessEq) -> (v1, v2, floor c)
      | _ -> (v1, v2, c)

    (* returns 'v1 ? v2 + c as (?, v1, v2, c) TODO more general *)
    let dl_edge pred =
      Message.print Message.Debug (lazy("SatDL: dl_edge for " ^ (print pred)));
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
        (kind, v1, v2, c2 -. c1)

    module Proof =
      struct
        type diff = predicate * expression * expression * float (* given predicate + edge (a - b <= c) *)
        type t = LEQ of predicate * domain * diff list
               | LT of predicate * domain * diff list (* also form NEQ proofs *)
               | EQ of predicate * domain * diff list * diff list (* two LEQ paths, a<=b /\ a>=b *)

        let mk_diff domain pred =
          let (v1, v2, c) = adapt_domain domain (dl_edge pred) in
            (pred, Variable v1, Variable v2, c)
        let pred_of_diff (p,_,_,_) = p
        
        let diff_to_string diff = print_pred (pred_of_diff diff)
        let path_to_string path = String.concat " " (List.map diff_to_string path)
        let to_string proof = match proof with
          | LEQ (pred, domain, diffs) | LT (pred, domain, diffs) ->
            (print_pred pred) ^ " because\n" ^ (path_to_string diffs)
          | EQ (pred, domain, diffs1, diffs2) ->
            (print_pred pred) ^ " because\n" ^ (path_to_string diffs1) ^ "\n" ^ (path_to_string diffs2)


        let get_left_diff (p,e1,e2,c) = e1
        let get_right_diff (p,e1,e2,c) = e2

        let get_left_path path = get_left_diff (List.hd path) 
        let get_right_path path = get_right_diff (List.hd (List.rev path))
        
        let get_left proof = match proof with
            | LEQ (_, _, path) | LT (_, _, path) -> get_left_path path
            | EQ (_, _, path1, path2) -> get_left_path path1
        let get_right proof = match proof with
            | LEQ (_, _, path) | LT (_, _, path) -> get_right_path path
            | EQ (_, _, path1, path2) -> get_left_path path2
        
        let get_domain prf = match prf with
          | LEQ (_, domain, _) | LT (_, domain, _) | EQ (_, domain, _, _) -> domain

        let sum_path path = List.fold_left (fun acc (_,_,_,c) -> acc +. c) 0.0 path

        let final_diff prf = match prf with
          | LEQ (pred, domain, path) | LT (pred, domain, path) -> mk_diff domain pred
          | EQ (pred, domain, path1, path2) ->
            let (_,e1,e2,c) = mk_diff domain pred in
              if e1 = (get_left_path path1) then
                begin
                  assert(e2 = get_right_path path1);
                  (pred, e1, e2, c)
                end
              else
                begin
                  assert(e2 = get_left_path path1);
                  (pred, e2, e1, -.c)
                end

        let well_formed prf =
          let diff_well_formed domain (pred, e1, e2, c) =
            let (_,e1',e2',c') = mk_diff domain pred in
              e1 = e1' && e2 = e2' && c >= c'
          in
          let is_path e1 e2 path =
            let a = (List.map (fun (_,a,_,_) -> a) path) @ [e2] in
            let b = e1 :: (List.map (fun (_,_,b,_) -> b) path) in
              (List.for_all2 (=) a b)
          in
          (*check path continuity and extremities TODO what about orientation of preds ?? *)
            match prf with
            | LEQ (pred, domain, path) ->
              begin
                let (_,e1,e2,c) = mk_diff domain pred in
                let c' = sum_path path in
                  (List.for_all (diff_well_formed domain) path) &&
                  (is_path e1 e2 path) &&
                  (c' <= c) 
              end
            | LT (pred, domain, path) ->
              begin
                let (_,e1,e2,c) = mk_diff domain pred in
                let c' = sum_path path in
                  (List.for_all (diff_well_formed domain) path) &&
                  (is_path e1 e2 path) &&
                  (c' < c) 
              end
            | EQ (pred, domain, path1, path2) ->
              begin
                let (_,e1,e2,c) = mk_diff domain pred in
                let c1 = sum_path path1 in
                let c2 = sum_path path2 in
                  (List.for_all (diff_well_formed domain) path1) &&
                  (List.for_all (diff_well_formed domain) path2) &&
                  (    ((is_path e1 e2 path1) && (is_path e2 e1 path2) && (c1 = c) && ((-.c) = c2))
                    || ((is_path e2 e1 path1) && (is_path e1 e2 path2) && (c2 = c) && ((-.c) = c1))
                  )
                  
              end

        (* only for eq given to the sovler.
         * TODO more: path 1 and path 2 form a cycle (that sums to 0).
         * for any to expression a,b in the path,
         * it possible to compute a predicate a = b + c, for some constant c *)
        let contains prf pred = match prf with
          | EQ (pred, domain, path1, path2) ->
            List.exists (fun (p,_,_,_) -> p = pred) (path1 @ path2)
          | _ -> false

        (** proof of what ? *)
        let of_what prf = match prf with
          | LEQ (p,_,_) | LT (p,_,_) | EQ (p,_,_,_) -> p

        let get_expr proof =
          let expr_from_diff (_,e1,e2,_) = (e1,e2) in
          let traverse path =
            List.fold_left
              (fun acc diff ->
                let e1,e2 = expr_from_diff diff in
                  ExprSet.add e1 (ExprSet.add e2 acc)
              )
              ExprSet.empty
              path
          in
            match proof with
            | LEQ (pred, _, path) | LT (pred, _, path) ->
              ExprSet.union (get_expr_set pred) (traverse path)
            | EQ (pred, domain, path1, path2) ->
              ExprSet.union
                (get_expr_set pred)
                (ExprSet.union (traverse path1) (traverse path2))

        let get_pred proof =
          let traverse path =
            List.fold_left
              (fun acc diff ->
                let p = pred_of_diff diff in
                  PredSet.add p acc
              )
              PredSet.empty
              path
          in
            match proof with
            | LEQ (pred, _, path) | LT (pred, _, path) ->
              PredSet.add pred (traverse path)
            | EQ (pred, domain, path1, path2) ->
              PredSet.add pred (PredSet.union (traverse path1) (traverse path2))

        (* Project paths on boundaries.
         * A proof of unsat is a negative cycle. *)
        let interpolate contradiction proof belongs_to =
          let domain = get_domain proof in
          let raw_path = match proof with
            | LT (_, _, path) | LEQ (_, _, path) -> path
            | _ -> failwith "SatDL.interpolate: expected LT or LEQ"
          in
          (* add the contradiction to the path to get a negative cycle *)
          let (p, e1, e2, c) as cdiff = mk_diff domain contradiction in
          let path =
            if (get_left_path raw_path) = e2 then
              cdiff :: raw_path
            else
              begin
                assert(get_right_path raw_path = e1);
                raw_path @ [cdiff]
              end
          in
          Message.print Message.Debug (lazy("SatDL.interpolate: path is " ^ (path_to_string path)));
          (* get the max of belongs_to. *)
          let maxExpr =
            List.fold_left
              (fun acc diff -> max acc (Interval.max (belongs_to (pred_of_diff diff))))
              1
              path 
          in
            if maxExpr <= 1 then
              (* contradiction local to first part only *)
              [False]
            else
              begin
                let is_eq p = match p with Eq _ -> true | _ -> false in
                let is_lt p = match p with Lt _ -> true | _ -> false in
                (* 1: determines how many boundaries there are 'max of belongs_to' -1, assuming belongs_to -> [1;\infty[ *)
                let boundaries = List.map (fun i -> (i,i+1)) (Utils.range 1 maxExpr) in
                (* take two consecutive diffs and compact them. *)
                let merge_diff diff1 diff2 =
                  let (p1,e11,e12,c1) = diff1 in
                  let (p2,e21,e22,c2) = diff2 in
                  let p, c = match domain with
                    | Integer ->
                      begin
                        let c = c1 +. c2 in
                        let p =
                          if (is_eq p1) && (is_eq p2) then Eq (e11, Sum [e22; Constant c])
                          else Leq (e11, Sum [e22; Constant c])
                        in
                          (simplify (p) , c)
                      end
                    | Real -> (*the cs might contain some epsilons ... *)
                      begin
                        let c1 = if is_lt p1 then c1 +. epsilon else c1 in
                        let c2 = if is_lt p2 then c2 +. epsilon else c2 in
                        let c = c1 +. c2 in
                        let p =
                          if (is_eq p1) && (is_eq p2) then Eq (e11, Sum [e22; Constant c])
                          else if (is_lt p1) && (is_lt p2) then Lt (e11, Sum [e22; Constant c])
                          else Leq (e11, Sum [e22; Constant c])
                        in
                        let c' = if (is_lt p1) && (is_lt p2) then c -. epsilon else c in
                          (simplify (p) , c')
                      end
                  in
                    assert ( e12 = e21 );
                    (p ,e11, e22, c)
                in
                (* a few methods to reason about where are the predicates *)
                let is_left_pred i pred =
                  let where = belongs_to pred in
                    (Interval.max where) <= i
                in
                (* 2: compact path to keep only relevant parts:
                 * the extremity of the path should be the same term, since a proof of unsat is a negative cylce.
                 * the path might also 'zigzag' between parts of the formula
                 * A side => project each part and take conj
                 * B side => project each part negate and take disj
                 * This version is A side. *)
                let rec split_path i acc_done acc_in_progess path = match path with
                  | ((px,_,_,_) as x)::((py,_,_,_) as y)::xs ->
                    begin
                      if (is_left_pred i px) = (is_left_pred i py) then (*accumulate*)
                        split_path i acc_done (x::acc_in_progess) (y::xs)
                      else (*split*)
                        split_path i ((List.rev (x::acc_in_progess)) :: acc_done) [] (y::xs)
                    end
                  | ((px,_,_,_) as x)::[] ->
                    begin
                      (*take the first and the last portion, and decide whether they should be merged.*)
                      match List.rev acc_done with
                      | (((py,_,_,_) as y) :: ys) :: accs ->
                        begin
                          if (is_left_pred i px) = (is_left_pred i py) then
                            ((List.rev (x::acc_in_progess)) @ (y::ys)) :: accs
                          else
                            (List.rev (x::acc_in_progess)) :: (y::ys) :: accs
                        end
                      | [] -> [List.rev (x::acc_in_progess)]
                      | _ -> failwith "SatDL.interpolate: empty portion of path."
                    end
                  | [] -> failwith "SatDL.interpolate: empty path"
                in
                let compact lst =
                  let diff = List.fold_left merge_diff (List.hd lst) (List.tl lst) in
                    pred_of_diff diff
                in
                  (*TODO assert that this is a negative cytcle.*)
                  List.map
                    (fun (i,i') ->
                      let split = split_path i [] [] path in
                      let a_side = List.filter (fun section -> is_left_pred i (pred_of_diff (List.hd section))) split in
                      let compacted = List.map compact a_side in
                        Message.print Message.Debug (lazy("SatDL.interpolate: boundary from " ^ (string_of_int i) ^ " to " ^ (string_of_int i')));
                        Message.print Message.Debug (lazy("SatDL.interpolate: split path is " ^ (String.concat "; " (List.map path_to_string split))));
                        And compacted
                    )
                    boundaries
              end

      end
    

    type t = {
      domain: domain;
      var_to_id: int StringMap.t;
      id_to_expr: expression IntMap.t;
      solver: BasicSolver.t;
      mutable partial_push: bool;
      mutable diff_to_pred: predicate DiffMap.t;
      history: predicate Stack.t
    }

    let to_string t =
      let buffer = Buffer.create 1000 in
      let add = Buffer.add_string buffer in
        add ("DL solver over "^(if t.domain = Real then "R" else "Z")^" :\n");
        add "  variables: ";
        StringMap.iter (fun k v -> add (k^"("^(string_of_int v)^"),")) t.var_to_id;
        add "\n";
        add (BasicSolver.to_string t.solver);
        Buffer.contents buffer

    let normalize_dl map pred =
      let (kind, v1, v2, c) = dl_edge pred in
      let id1 = StringMap.find v1 map in
      let id2 = StringMap.find v2 map in
        (kind, id1, id2, c)

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
      let expand p = match p with
        | (Equal, v1, v2, c) -> (LessEq, v1, v2,  c) :: (LessEq, v2, v1, -.c) :: (LessStrict, v1, v2,  c) :: (LessStrict, v2, v1, -.c) :: []
        | (LessEq, v1, v2, c) -> (LessEq, v1, v2,  c) :: (LessStrict, v2, v1, -.c) :: []
        | (LessStrict, v1, v2, c) -> (LessStrict, v1, v2,  c) :: (LessEq, v2, v1, -.c) :: []
      in
      let history = Stack.create () in
      let cstrs = PredSet.elements (get_literal_set (And preds)) in
      let raw_diffs = List.map (normalize_dl var_to_id) cstrs in
      let all_diffs = List.flatten (List.map expand raw_diffs) in
      let final_diffs = List.map (adapt_domain domain) all_diffs in
      let solver = BasicSolver.create final_diffs in
        (* z_0 = 0 ? *)
        {
          domain = domain;
          var_to_id = var_to_id;
          id_to_expr = id_to_expr;
          history = history;
          partial_push = false;
          diff_to_pred = DiffMap.empty;
          solver = solver
        }
    
    (* methods to convert from diff to pred ... *)
    let register t diff pred =
      if not (DiffMap.mem diff t.diff_to_pred) then
        t.diff_to_pred <- DiffMap.add diff pred t.diff_to_pred

    let get_pred t diff =
      try DiffMap.find diff t.diff_to_pred
      with Not_found ->
        begin
          Message.print Message.Debug (lazy("SatDL: get_pred Not_found " ^ (Diff.to_string diff)));
          let (v1,v2,c) = diff in
          let v1 = IntMap.find v1 t.id_to_expr in
          let v2 = IntMap.find v2 t.id_to_expr in
            Leq(Sum[v1; Coeff (-1.0, v2)], Constant c)
        end

    let deregister t pred =
      let raw_diff = normalize_dl t.var_to_id pred in
      let diff = adapt_domain t.domain raw_diff in
      let p' = get_pred t diff in
        if p' = pred then t.diff_to_pred <- DiffMap.remove diff t.diff_to_pred

    let push t pred =
      assert(BasicSolver.is_sat t.solver && t.partial_push = false);
      Message.print Message.Debug (lazy("SatDL: pushing " ^ (print_pred pred)));
      let (kind, v1, v2, c) = normalize_dl t.var_to_id pred in
        Stack.push pred t.history;
        match kind with
        | Equal ->
          let diff1 = adapt_domain t.domain (LessEq,v1,v2,c) in
          let res1 = BasicSolver.push t.solver diff1 in
            register t diff1 pred;
            if res1 then
              begin
                let diff2 = adapt_domain t.domain (LessEq,v2,v1,-.c) in
                  register t diff2 pred;
                  BasicSolver.push t.solver diff2
              end
            else
              begin
                t.partial_push <- true;
                false
              end
        | LessStrict | LessEq ->
          let diff = adapt_domain t.domain (kind,v1,v2,c) in
            register t diff pred;
            BasicSolver.push t.solver diff

    let pop t =
      let p = Stack.pop t.history in
        deregister t p;
        match p with
        | Eq _ ->
          BasicSolver.pop t.solver;
          if not t.partial_push
          then BasicSolver.pop t.solver
          else t.partial_push <- false
        | _ ->
          assert(t.partial_push = false);
          BasicSolver.pop t.solver

    let is_sat t = BasicSolver.is_sat t.solver

    let propagations t shared =
      Message.print Message.Debug (lazy("SatDL: propagations on " ^ (String.concat "," (List.map print_expr shared))));
      let indexes =
        List.map
          (fun x -> match x with Variable s -> StringMap.find s t.var_to_id | _ -> failwith "SatDL, propagations: expected Variable")
          shared
      in
      let propagated = BasicSolver.propagations t.solver indexes in
        List.map (fun (a,b) -> order_eq (Eq (IntMap.find a t.id_to_expr, IntMap.find b t.id_to_expr))) propagated


    let entailed t pred =
      Message.print Message.Debug (lazy("SatDL: entailed " ^ (print_pred pred)));
      let (kind, v1, v2, c) = normalize_dl t.var_to_id pred in
        match kind with
        | Equal ->
          let diff1 = adapt_domain t.domain (kind,v1,v2,c) in
          let diff2 = adapt_domain t.domain (kind,v2,v1,-.c) in
            BasicSolver.entailed t.solver diff1 &&
            BasicSolver.entailed t.solver diff2
        | LessStrict | LessEq ->
          let diff = adapt_domain t.domain (kind,v1,v2,c) in
            BasicSolver.entailed t.solver diff


    (* core => Not contradiction *)
    let justify t pred =
      Message.print Message.Debug (lazy("SatDL: justify " ^ (print_pred pred)));
      let (kind, v1, v2, c) = normalize_dl t.var_to_id pred in
      let (core, deductions) =
        match kind with
        | Equal ->
          let diff1 = adapt_domain t.domain (kind,v1,v2,c) in
          let diff2 = adapt_domain t.domain (kind,v2,v1,-.c) in
          let proof1 = BasicSolver.mk_proof t.solver diff1 in
          let proof2 = BasicSolver.mk_proof t.solver diff2 in
          let given_diffs = (BasicSolver.Proof.path proof1) @ (BasicSolver.Proof.path proof2) in
          let given = List.fold_left (fun acc d -> DiffSet.add d acc) DiffSet.empty given_diffs in
            (given, [])
        | LessStrict | LessEq ->
          let diff = adapt_domain t.domain (kind,v1,v2,c) in
          let proof = BasicSolver.mk_proof t.solver diff in
          let given = List.fold_left (fun acc d -> DiffSet.add d acc) DiffSet.empty (BasicSolver.Proof.path proof) in
            (given, [])
      in
      let core_pred = OrdSet.remove_duplicates (List.map (get_pred t) (DiffSet.elements core)) in
      let contradiction = normalize (Not pred) in
        (And core_pred, contradiction, DL, deductions)

    (*transform a proof from the BasicSolver to a partial proof of the InterfaceLayer
     *this transform returns a predicate (implied by the proof), domain, and diff list. *)
    let transform_proof t prf =
      Message.print Message.Debug (lazy ("SatDL.Proof transforming: " ^ (BasicSolver.Proof.to_string prf)));
      let proven = get_pred t (BasicSolver.Proof.what prf) in
      let proof = BasicSolver.Proof.path prf in
      let diff_to_diff diff =
        let pred = get_pred t diff in
        let a = IntMap.find (Diff.a diff) t.id_to_expr in
        let b = IntMap.find (Diff.b diff) t.id_to_expr in
        let c = Diff.c diff in
          (pred, a, b, c)
      in
        (proven, t.domain, List.map diff_to_diff proof)
    
    let unsat_core_with_info_proof t =
      let (diff, proof) = BasicSolver.unsat_core_with_info t.solver in (* proof |= ~diff *)
      let contradiction = get_pred t diff in
      let (_, domain, proof') = transform_proof t proof in
      let proof2 = Proof.LT (contradiction, domain, proof') in
      let core_pred = PredSet.elements (PredSet.add contradiction (Proof.get_pred proof2)) in
        Message.print Message.Debug (lazy ("SatDL basic contra: " ^ (Diff.to_string diff)));
        Message.print Message.Debug (lazy ("SatDL basic proof: " ^ (BasicSolver.Proof.to_string proof)));
        Message.print Message.Debug (lazy ("SatDL result: " ^ (Proof.to_string proof2)));
        (normalize_only (And core_pred), contradiction, DL, proof2)
    
    (* TODO does not need to return the proof ??? *)
    let unsat_core_with_info t =
      let (core, contradiction, th, _) = unsat_core_with_info_proof t in
        (core, contradiction, th, [])

    let mk_proof t pred =
      Message.print Message.Debug (lazy("SatDL: mk_proof" ^ (print_pred pred)));
      let (kind, v1, v2, c) = normalize_dl t.var_to_id pred in
      let proof =
        match kind with
        | Equal ->
          let diff1 = adapt_domain t.domain (kind,v1,v2,c) in
          let diff2 = adapt_domain t.domain (kind,v2,v1,-.c) in
          let proof1 = BasicSolver.mk_proof t.solver diff1 in
          let proof2 = BasicSolver.mk_proof t.solver diff2 in
          let (_, _, proof1') = transform_proof t proof1 in
          let (_, _, proof2') = transform_proof t proof2 in
            Proof.EQ (pred, t.domain, proof1', proof2')
        | LessStrict ->
          let diff = adapt_domain t.domain (kind,v1,v2,c) in
          let proof = BasicSolver.mk_proof t.solver diff in
          let (_, _, proof') = transform_proof t proof in
            Proof.LEQ (pred, t.domain, proof')
        | LessEq ->
          let diff = adapt_domain t.domain (kind,v1,v2,c) in
          let proof = BasicSolver.mk_proof t.solver diff in
          let (_, _, proof') = transform_proof t proof in
            Proof.LT (pred, t.domain, proof')
      in
        proof

  end

(*TODO put some tests here*)
(*
let test =
  Message.enable_debug ();
  let a_pred1 = Leq (Variable "a", Constant 0.0) in
  let a_pred2 = Leq (Constant 1.0, Variable "b") in
  let a_preds = [a_pred1; a_pred2] in
  let b_pred = Lt (Variable "b", Variable "a") in
  let b_preds = [b_pred] in
  let domain = InterfaceLayer.Real in
  let solver = InterfaceLayer.create domain (a_preds @ b_preds) in
    assert(InterfaceLayer.push solver a_pred1);
    assert(InterfaceLayer.push solver a_pred2);
    assert(not (InterfaceLayer.push solver b_pred));
    let core, contra, _, proof = InterfaceLayer.unsat_core_with_info_proof solver in
    let belongs_to p =
      if List.mem p a_preds then
        if List.mem p b_preds then (1,2) else (1,1)
      else (2,2)
    in
    let itp = InterfaceLayer.Proof.interpolate contra proof belongs_to in
      Message.print Message.Normal (lazy ("proof = " ^ (InterfaceLayer.Proof.to_string proof)));
      Message.print Message.Normal (lazy ("core = " ^ (print_pred core)));
      Message.print Message.Normal (lazy ("contra = " ^ (print_pred contra)));
      Message.print Message.Normal (lazy ("itp = " ^ (print_pred (List.hd itp))))
*)
