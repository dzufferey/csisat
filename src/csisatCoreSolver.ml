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

(** Core solver
 * handles natively the EUF theory,
 * can use other theory solvers,
 * interacts with the satsolver.
 *)

open   CsisatAst
(**/**)
module Global  = CsisatGlobal
module AstUtil = CsisatAstUtil
module PredSet = CsisatAstUtil.PredSet
module ExprSet = CsisatAstUtil.ExprSet
module Message = CsisatMessage
module Utils   = CsisatUtils
module IntSet  = CsisatUtils.IntSet
module OrdSet  = CsisatOrdSet
module EqDag   = CsisatDag
module Dpll    = CsisatDpllCore
(**/**)

(** The different changes that can happen in the system *)
type find_t =  int * (predicate list)
type sat_changes = Equal of (int * find_t * IntSet.t) * (int * find_t * IntSet.t) (* 2 x (id,find,ccpar) *)
                 | ImplyNotEqual of (int * int) (* for instance a < b ==> ~(a = b) *)
                 | SentToTheory of theory * predicate (* what was sent to which solver *)
type change = StackSat of predicate * (sat_changes list) (* predicate given by sat solver *)
            | StackTDeduction of predicate * theory * (int * find_t * IntSet.t) * (int * find_t * IntSet.t) (* theory deduction (one equality) TODO how to extend this to non convex theories *)
            | StackInternal of int * find_t (* path compression: (id, old find) *)

module Node =
  struct
    type t = {
      id: int;
      fn: string;
      args: int list;
      arity: int;
      expr: expression;
      nodes: t array;
      events: euf_change Stack.t;
      mutable find: find_t; (*the predicate list is used to construct the unsat core faster *)
      mutable ccpar: IntSet.t
    }

    (*val create: expression -> int -> string -> int list -> t array -> euf_change Stack.t -> t*)
    let create expr id fn args nodes events = {
      id = id;
      fn = fn;
      args = args;
      arity = List.length args;
      expr = expr;
      nodes = nodes;
      events = events;
      find = (id, []);
      ccpar = IntSet.empty;
    }
    
    (*val copy: t -> t*)
    let copy n = {
      id = n.id;
      fn = n.fn;
      args = n.args;
      arity = n.arity;
      expr = n.expr;
      nodes = n.nodes;
      events = n.events;
      find = n.find;
      ccpar = n.ccpar;
    }
    
    (*TODO is it right ?? (predicate update) *)
    (*val find: t -> t*)
    let rec find this =
      if (fst this.find) = this.id then this
      else
        begin
          let p = this.nodes.(fst this.find) in
          let top = find p in
            Stack.push (StackInternal (this.id, this.find)) (this.events);
            this.find <- (top.id, (snd p.find) @ (snd this.find));
            top
        end

    (*TODO is it right ?? (predicate update) *)
    (*val union: t -> t -> (t * t)*)
    let union this that = 
      let n1 = find this in
      let n2 = find that in
      let on1 = copy n1 in
      let on2 = copy n2 in
      let eq = AstUtil.order_eq (Eq (this.expr, that.expr)) in
        n1.find <- (n2.id, eq :: (snd this.find) @ (snd that.find));
        n2.ccpar <- (IntSet.union n1.ccpar n2.ccpar);
        n1.ccpar <- IntSet.empty;
        (on1, on2)

    (*val ccpar: t -> IntSet.t*)
    let ccpar node = (find node).ccpar

    (*val congruent: t -> t -> bool*)
    let congruent this that =
        this.fn = that.fn
      &&
        this.arity = that.arity
      &&
        List.for_all
          (fun (a,b) -> (find a).id = (find b).id)
          (List.rev_map2 (fun x y -> (this.nodes.(x), this.nodes.(y))) (this.args) (that.args))

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    (*val may_be_congruent: t -> t -> (t * t) list*)
    let may_be_congruent this that =
      if this.fn <> that.fn
      || this.arity <> that.arity
      || (find this).id = (find that).id then []
      else
        List.filter
          (fun (a,b) -> (find a).id <> (find b).id)
          (List.rev_map2 (fun x y -> (this.nodes.(x), this.nodes.(y))) (this.args) (that.args))

    (** return pairs of nodes whose equality comes from congruence*)
    (*val merge: t -> t -> unit*)
    let merge this that =
      (* always report the first equality *)
      Stack.push
        (StackEq (AstUtil.order_eq (Eq (this.expr, that.expr)), (this.id, this.find, this.ccpar), (that.id, that.find, that.ccpar)))
        (this.events);
      let first_to_stack _ _ _ _ = () in
      let other_to_stack a b changed_a changed_b =
        Stack.push
          (StackTDeduction (AstUtil.order_eq (Eq (a.expr, b.expr)), (changed_a.id, changed_a.find, changed_a.ccpar), (changed_b.id, changed_b.find, changed_b.ccpar)))
          a.events
      in
      let rec process to_stack this that =
        if (find this).id <> (find that).id then
          begin
            let p1 = ccpar this in
            let p2 = ccpar that in
            let (a,b) = union this that in
              to_stack this that a b; (* report changes *)
              let to_test = Utils.cartesian_product (IntSet.elements p1) (IntSet.elements p2) in
                List.iter
                  (fun (x,y) ->
                    let x = this.nodes.(x) in
                    let y = this.nodes.(y) in
                      if (find x).id <> (find y).id && congruent x y then
                        process other_to_stack x y
                  )
                  to_test
          end
      in
        process first_to_stack this that 
  end

(*TODO firs make it work for EUF, then extend to EUF + T *)
module CoreSolver: sig
    type t
    val create: predicate -> t
    val get: t -> int -> Node.t
    val get_node: t -> expression -> Node.t
    val is_sat: t -> bool
    val push: t -> predicate -> bool
    val pop: t -> unit
    val propagation: t -> predicate list (*propagates only on the variables known b the sat solver. *)
  end
  =
  struct
    type t = {
      sat_solver: Dpll.csi_dpll;
      nodes: Node.t array;
      mutable expr_to_node: Node.t ExprMap.t;(*TODO not really mutable*)
      stack: change Stack.t;
      mutable neqs: (int * int) list (* neqs as pairs of node id *)
      mutable explanations: (predicate * theory * (predicate * theory) list) PredMap.t
      (* TODO what is needed for the theory splitting and theory solvers *)
      (* a theory solver being a module, there are some problem
       * Functors: modular, but only handles a fixed number of solver
       * class: modular, dynamic dispatch
       * explicitely listing all possible solver: not modular, but can take advantage of the specificties of each theories.
       *)
    }

    (*TODO split the theories and keep what belongs to what*)
    let create pred =
      let pset = AstUtil.get_proposition_set pred in
      let set =
        PredSet.fold
          (fun p acc -> ExprSet.union (CsisatAstUtil.get_expr_deep_set p) acc)
          pset
          ExprSet.empty
      in
      let id = ref 0 in
      let graph = {
          sat_solver = new Dpll.csi_dpll true;
          nodes = Array.make
            (ExprSet.cardinal set)
            (Node.create (Constant (-1.)) (-1) "Dummy" [] [||] (Stack.create ()));
          expr_to_node = ExprMap.empty;
          stack = Stack.create ();
          neqs = [];
        }
      in
      let create_and_add expr fn args =
        try ExprMap.find expr graph.expr_to_node
        with Not_found ->
          begin
            let n = Node.create expr !id fn args graph.nodes graph.stack in
              graph.nodes.(!id) <- n;
              id := !id + 1;
              graph.expr_to_node <- ExprMap.add expr n graph.expr_to_node;
              n
          end
      in
      let rec convert_exp expr = match expr with
        | Constant c as cst -> create_and_add cst (string_of_float c) []
        | Variable v as var -> create_and_add var v []
        | Application (f, args) as appl ->
          let node_args = List.map (fun x -> x.Node.id) (List.map convert_exp args) in
          let new_node  = create_and_add appl f node_args in
            new_node
        | Sum lst as sum ->
          let node_args = List.map (fun x -> x.Node.id) (List.map convert_exp lst) in
          let new_node  = create_and_add sum "+" node_args in
            new_node
        | Coeff (c, e) as coeff ->
          let node_args = List.map (fun x -> x.Node.id) (List.map convert_exp  [Constant c; e]) in
          let new_node  = create_and_add coeff "*" node_args in
            new_node
      in
      let _ = ExprSet.iter (fun x -> ignore (convert_exp x)) set in
        graph

    let get dag i = dag.nodes.(i)
    let get_node dag expr = ExprMap.find expr dag.expr_to_node

    let is_euf_sat dag =
      not (
        List.exists
          (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
          dag.neqs
      )    

    let push dag pred =
      if not (is_sat dag) then failwith "CoreSolver: push called on an already unsat system.";
      failwith "TODO"

    let pop dag =
      let undo (id, find, parent) =
        let n = get dag id in
          n.Node.find <- find;
          n.Node.ccpar <- parent
      in
      let rec process () =
        if Stack.is_empty dag.stack then
          failwith "CoreSolver: pop called on an empty stack"
        else
          begin
            let t = Stack.pop dag.stack in
              match t with
              | StackInternal (id, find) ->
                begin
                  (get dag id).Node.find <- find;
                  process ()
                end
              | _ -> failwith ("CoreSolver: TODO")
          end
      in
        process ()

    (* Propagation on given variables ...
     * the given expressions are assumed to be not kown equal
     * TODO predicates ... *)
    let propagation dag variables =
      let var_nodes = List.map (get_node dag) variables in
      let rec process_nodes acc lst = match lst with
        | x::xs ->
          begin
            let x_class = (Node.find x).Node.id in
            let same,rest = List.partition (fun n -> (Node.find n).Node.id = x_class) xs in
            let deductions = List.map (fun n -> AstUtil.order_eq (Eq (x.Node.expr, n.Node.expr))) same in
              process_nodes (deductions @ acc) rest
          end
        | [] -> acc
      in
        process_nodes [] var_nodes
    
    let is_theory_consistent t = is_euf_sat t

    (* has a satisfiable assignement *)
    let is_sat t = t.dpll#is_sat && is_theory_consistent t

    (* partially sat / no explicit contradiction *)
    let is_consistent t = t.dpll#is_consistent && is_theory_consistent t

    let euf_lemma_with_info dag =
      let (c1,c2) = try
          List.find
            (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
            dag.neqs
        with Not_found ->
          failwith "EUF, unsat_core_with_info: system is sat!"
      in
      let contradiction = AstUtil.order_eq (Not (Eq ((get dag c1).Node.expr,(get dag c2).Node.expr))) in
      let raw_congruences = congruences dag in
      let all_congruences = OrdSet.list_to_ordSet raw_congruences in
      let raw_core = OrdSet.list_to_ordSet ((snd (get dag c1).Node.find) @ (snd (get dag c2).Node.find)) in
      (* raw_core contains both given equalities and congruences.
       * it is an overapproximation ...
       * TODO improve -> do a search for eq paths that makes the contradiction possible
       *)
      let needed_congruences = OrdSet.intersection all_congruences raw_core in
      let congruences = List.filter (fun x -> OrdSet.mem x needed_congruences) raw_congruences in (*keep congruence in order*)
      let info = List.map (fun x -> (x,EUF)) congruences in
      let core = contradiction :: (OrdSet.subtract raw_core congruences) in
        (And core, EUF, info)

    (* blocking clause *)
    let theory_lemma t = euf_lemma_with_info t

    type solved = Sat of predicate list
                | Unsat of DpllCore.res_proof * (predicate * theory * (predicate * theory) list) PredMap.t

    let rec solve t =
      if is_consistent t then
        begin
          if is_sat t then
            Sat t.dpll#get_solution
          else
            match t.dpll#next with
            | Affected lst -> (*TODO push to the theories *)
              failwith "TODO"
            | Affectation (lst1,lst2) -> (*TODO push to the theories is sat then return the assign *)
              failwith "TODO"
            | Backtracked howmany ->
              let new_state = List.fold_left (fun _ -> pop t) (Utils.range 0 howmany) in
                solve new_state
            | Proof proof -> Unsat (proof, t.explanations)
        end
      else
        begin
          assert (has_theory_contradiction t);
          let (new_clause, explanation) = theory_lemma t in
            t.explanations <- PredMap.add new_clause explanation t.explanations;
            t.dpll#add_clause new_clause;
            match t.dpll#next with
            | Backtracked howmany ->
              let new_state = List.fold_left (fun _ -> pop t) (Utils.range 0 howmany) in
                solve new_state
            | Proof proof -> Unsat (proof, t.explanations)
            | _ -> failwith "expecting Backtracked of Proof"
        end
  end

