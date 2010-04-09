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

module Node : sig
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
    
    val create: expression -> int -> string -> int list -> t array -> euf_change Stack.t -> t
    val copy: t -> t
    val find: t -> t
    val union: t -> t -> (t * t)
    val ccpar: t -> IntSet.t
    val congruent: t -> t -> bool
    val may_be_congruent: t -> t -> (t * t) list
    val merge: t -> t -> unit
  end
  =
  struct
    type t = {
      id: int;
      fn: string;
      args: int list;
      arity: int;
      expr: expression;
      nodes: t array;
      events: euf_change Stack.t;
      mutable find: find_t;
      mutable ccpar: IntSet.t
    }

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

    let ccpar node = (find node).ccpar

    let congruent this that =
        this.fn = that.fn
      &&
        this.arity = that.arity
      &&
        List.for_all
          (fun (a,b) -> (find a).id = (find b).id)
          (List.rev_map2 (fun x y -> (this.nodes.(x), this.nodes.(y))) (this.args) (that.args))

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    let may_be_congruent this that =
      if this.fn <> that.fn
      || this.arity <> that.arity
      || (find this).id = (find that).id then []
      else
        List.filter
          (fun (a,b) -> (find a).id <> (find b).id)
          (List.rev_map2 (fun x y -> (this.nodes.(x), this.nodes.(y))) (this.args) (that.args))

    (** return pairs of nodes whose equality comes from congruence*)
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

module CoreSolver: sig
    type t = {
      sat_solver: Dpll.csi_dpll;
      nodes: Node.t array;
      expr_to_node: (expression, Node.t) Hashtbl.t;
      stack: change Stack.t;
      mutable neqs: (int * int) list (* neqs as pairs of node id *)
      (* TODO what is needed for the theory splitting and theory solvers *)
      (* a theory solver being a module, there are some problem
       * Functors: modular, but only handles a fixed number of solver
       * class: modular, dynamic dispatch
       * explicitely listing all possible solver: not modular, but can take advantage of the specificties of each theories.
       *)
    }

    val create: PredSet.t -> t
    val get: t -> int -> Node.t
    val get_node: t -> expression -> Node.t
    val is_sat: t -> bool
    val push: t -> predicate -> bool
    val pop: t -> unit
    val propagation: t -> predicate list (*propagates only on the variables known b the sat solver. *)
    val unsat_core_with_info: t -> (predicate * theory * (predicate * theory) list)
    val unsat_core: t -> predicate
  end
  =
  struct
    type t = {
      sat_solver: Dpll.csi_dpll;
      nodes: Node.t array;
      expr_to_node: (expression, Node.t) Hashtbl.t;
      stack: change Stack.t;
      mutable neqs: (int * int) list
    }

    (*TODO split the theories and keep what belongs to what*)
    let create pset =
      let set =
        PredSet.fold
          (fun p acc -> ExprSet.union (CsisatAstUtil.get_expr_deep_set p) acc)
          pset
          ExprSet.empty
      in
      let id = ref 0 in
      let table1 = Hashtbl.create (ExprSet.cardinal set) in
      let graph = {
          sat_solver = new Dpll.csi_dpll true;
          nodes = Array.make
            (ExprSet.cardinal set)
            (Node.create (Constant (-1.)) (-1) "Dummy" [] [||] (Stack.create ()));
          expr_to_node = table1;
          stack = Stack.create ();
          neqs = [];
        }
      in
      let create_and_add expr fn args =
        try Hashtbl.find table1 expr
        with Not_found ->
          begin
            let n = Node.create expr !id fn args graph.nodes graph.stack in
              graph.nodes.(!id) <- n;
              id := !id + 1;
              Hashtbl.replace table1 expr n;
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
    let get_node dag expr = Hashtbl.find dag.expr_to_node expr

    let is_sat dag =
      not (
        List.exists
          (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
          dag.neqs
      ) && failwith "TODO what about the theories"
    
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
    
    let unsat_core_with_info dag = failwith "TODO"

    let unsat_core dag = 
      let (core, _, _) = unsat_core_with_info dag in
        core
  end

