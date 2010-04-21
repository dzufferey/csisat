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
module PredMap = CsisatAstUtil.PredMap
module ExprMap = CsisatAstUtil.ExprMap
module Message = CsisatMessage
module Utils   = CsisatUtils
module IntSet  = CsisatUtils.IntSet
module OrdSet  = CsisatOrdSet
module EqDag   = CsisatDag
module Dpll    = CsisatDpllCore
module DpllProof = CsisatDpllProof
(**/**)

(** The different changes that can happen in the system *)
type find_t =  Leader of PredSet.t * PredSet.t (*all given predicates, all congruences*)
            |  Member of int (*representative is int*)
type sat_changes = Equal of (int * find_t * IntSet.t) * (int * find_t * IntSet.t) (* 2 x (id,find,ccpar) *)
                 | ImplyNotEqual of (int * int) (* for instance a < b ==> ~(a = b) *)
                 | SentToTheory of theory * predicate (* what was sent to which solver *)
type change = StackSat of predicate * sat_changes list (* predicate given by sat solver *)
            | StackTDeduction of predicate * theory * (int * find_t * IntSet.t) * (int * find_t * IntSet.t) (* theory deduction (one equality) TODO how to extend this to non convex theories *)
            | StackInternal of int * find_t (* path compression: (id, old find) TODO all the changes at once *)

module Node =
  struct
    type t = {
      id: int;
      fn: string;
      args: int list;
      arity: int;
      expr: expression;
      nodes: t array;
      events: change Stack.t;
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
      find = Leader (PredSet.empty, PredSet.empty);
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

    let to_string n =
      "node "^(string_of_int n.id)^
      " ("^(AstUtil.print_expr n.expr)^") "^
      n.fn^"("^(String.concat ", "(List.map string_of_int n.args))^") "^
      " ccpar = {"^(String.concat ", " (List.map string_of_int (IntSet.elements n.ccpar)))^"}"


    let set_ccparent node set = node.ccpar <- set
    let add_ccparent node n = node.ccpar <- (IntSet.add n node.ccpar)
    let get_ccparent node = node.ccpar

    
    (*val find: t -> t*)
    let rec find this = match this.find with
      | Leader _ -> this
      | Member id ->
        begin
          let top = find (this.nodes.(id)) in
            Stack.push (StackInternal (this.id, this.find)) (this.events);
            this.find <- Member top.id;
            top
        end

    let get_find_predicates n = match n.find with
      | Leader (p1,p2) -> (p1,p2)
      | Member _ -> failwith "get_find_predicates: only for leaders"


    (*val union: t -> t -> (t * t)*)
    let union preds congruence this that = 
      let n1 = find this in
      let n2 = find that in
      let g1, c1 = get_find_predicates n1 in
      let g2, c2 = get_find_predicates n2 in
        n2.find <- Leader (PredSet.union preds (PredSet.union g1 g2), PredSet.union congruence (PredSet.union c1 c2));
        n1.find <- Member n2.id;
        n2.ccpar <- (IntSet.union n1.ccpar n2.ccpar);
        n1.ccpar <- IntSet.empty

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

    let small_justification (set, _) this that =
      if this.id = that.id then PredSet.empty
      else
        let eq = AstUtil.order_eq (Eq (this.expr, that.expr)) in
          if PredSet.mem eq set then PredSet.singleton eq
          else set (*TODO better -> shortest path (if no congruence)*)

    let explain_congruence this that =
      assert (Global.is_off_assert() || congruent this that);
      List.fold_left2
        (fun acc a b ->
          let a = this.nodes.(a) in
          let b = this.nodes.(b) in
          let set = get_find_predicates (find a) in
            PredSet.union acc (small_justification set a b)
        )
        PredSet.empty
        this.args
        that.args

    (** return pairs of nodes whose equality comes from congruence*)
    (*val merge: t -> t -> unit*)
    let merge this that =
      (* always report the first equality *)
      let mk_eq a b = AstUtil.order_eq (Eq (a.expr, b.expr)) in
      let mk_eq_set a b = PredSet.singleton (mk_eq a b) in
      Message.print Message.Debug (lazy("CoreSolver: merge given " ^ (AstUtil.print_pred (mk_eq this that))));
      let first_to_stack _ _ _ _ = () in
      let other_to_stack a b changed_a changed_b =
        Message.print Message.Debug (lazy("CoreSolver: merge congruence " ^ (AstUtil.print_pred (mk_eq a b))));
        Stack.push
          (StackTDeduction (mk_eq a b, EUF, (changed_a.id, changed_a.find, changed_a.ccpar), (changed_b.id, changed_b.find, changed_b.ccpar)))
          a.events
      in
      let rec process to_stack pred congruence this that =
        let n1 = find this in
        let n2 = find that in
          if n1.id <> n2.id then
            begin
              let p1 = ccpar n1 in
              let p2 = ccpar n2 in
                to_stack this that n1 n2; (* report changes *)
                union pred congruence n1 n2;
                let to_test = Utils.cartesian_product (IntSet.elements p1) (IntSet.elements p2) in
                  Message.print Message.Debug (lazy(
                    "CoreSolver: merge to_test " ^
                    (String.concat ", "
                      (List.map
                        (fun (x,y) -> AstUtil.print_pred (AstUtil.order_eq (Eq (this.nodes.(x).expr, this.nodes.(y).expr))))
                        to_test))));
                  List.iter
                    (fun (x,y) ->
                      let x = this.nodes.(x) in
                      let y = this.nodes.(y) in
                        if (find x).id <> (find y).id && congruent x y then
                          process other_to_stack (explain_congruence x y) (mk_eq_set x y) x y
                    )
                    to_test
          end
      in
        process first_to_stack (mk_eq_set this that) PredSet.empty this that 
  end

(*TODO firs make it work for EUF, then extend to EUF + T *)
module CoreSolver =
  struct
    type t = {
      sat_solver: Dpll.csi_dpll;
      nodes: Node.t array;
      expr_to_node: Node.t ExprMap.t;(*TODO not really mutable*)
      stack: change Stack.t;
      mutable neqs: (int * int) list; (* neqs as pairs of node id *)
      mutable explanations: (predicate * theory * (predicate * theory) list) PredMap.t
      (* TODO what is needed for the theory splitting and theory solvers *)
      (* a theory solver being a module, there are some problem
       * Functors: modular, but only handles a fixed number of solver
       * class: modular, dynamic dispatch
       * explicitely listing all possible solver: not modular, but can take advantage of the specificties of each theories.
       *)
    }

    let euf_to_string dag =
      let buffer = Buffer.create 1000 in
      let add = Buffer.add_string buffer in
        add "EUF:\n";
        Array.iter (fun x -> add (Node.to_string x); add "\n") dag.nodes;
        Buffer.contents buffer

    (*TODO split the theories and keep what belongs to what
     *TODO equisat
     *)
    let create pred =
      let pset = CsisatAstUtil.get_proposition_set pred in
      let set =
        PredSet.fold
          (fun p acc -> ExprSet.union (CsisatAstUtil.get_expr_deep_set p) acc)
          pset
          ExprSet.empty
      in
      let id = ref 0 in
      let sat_solver = new Dpll.csi_dpll true in
      let nodes = Array.make
        (ExprSet.cardinal set)
        (Node.create (Constant (-1.)) (-1) "Dummy" [] [||] (Stack.create ()))
      in
      let expr_to_node = ref ExprMap.empty in
      let stack = Stack.create () in
      let create_and_add expr fn args =
        try ExprMap.find expr !expr_to_node
        with Not_found ->
          begin
            let node_args = List.map (fun x -> x.Node.id) args in
            let n = Node.create expr !id fn node_args nodes stack in
              nodes.(!id) <- n;
              id := !id + 1;
              expr_to_node := ExprMap.add expr n !expr_to_node;
              List.iter (fun a -> Node.add_ccparent a n.Node.id) args;
              n
          end
      in
      let rec convert_exp expr = match expr with
        | Constant c as cst -> create_and_add cst (string_of_float c) []
        | Variable v as var -> create_and_add var v []
        | Application (f, args) as appl ->
          let node_args = List.map convert_exp args in
          let new_node  = create_and_add appl f node_args in
            new_node
        | Sum lst as sum ->
          let node_args = List.map convert_exp lst in
          let new_node  = create_and_add sum "+" node_args in
            new_node
        | Coeff (c, e) as coeff ->
          let node_args = List.map convert_exp  [Constant c; e] in
          let new_node  = create_and_add coeff "*" node_args in
            new_node
      in
      let _ = ExprSet.iter (fun x -> ignore (convert_exp x)) set in
      let graph = {
          sat_solver = sat_solver;
          nodes = nodes;
          expr_to_node = !expr_to_node;
          stack = stack;
          neqs = [];
          explanations = PredMap.empty
        }
      in
      let f =
        if AstUtil.is_cnf pred then pred 
        else match AstUtil.equisatisfiable pred with
          | (_,_,f) -> f
      in
      let f = AstUtil.cnf (AstUtil.simplify f) in
        sat_solver#init f;
        Message.print Message.Debug (lazy("CoreSolver: " ^ (euf_to_string graph)));
        graph

    let get dag i = dag.nodes.(i)
    let get_node dag expr = ExprMap.find expr dag.expr_to_node

    let is_euf_sat dag =
      not (
        List.exists
          (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
          dag.neqs
      )    
    
    let is_theory_consistent t = is_euf_sat t

    (* has a satisfiable assignement *)
    let is_sat t = t.sat_solver#is_sat && is_theory_consistent t

    (* partially sat / no explicit contradiction *)
    let is_consistent t = t.sat_solver#is_consistent && is_theory_consistent t


    let push dag pred =
      Message.print Message.Debug (lazy("CoreSolver: push " ^ (AstUtil.print_pred pred)));
      if not (is_theory_consistent dag) then failwith "CoreSolver: push called on an already unsat system."
      else
        begin
          match pred with
          | Eq(e1,e2) ->
            begin
              let n1 = get_node dag e1 in
              let n2 = get_node dag e2 in
              let n1' = Node.find n1 in
              let n2' = Node.find n2 in
                Stack.push
                  (StackSat (pred,  [Equal ((n1'.Node.id, n1'.Node.find, n1'.Node.ccpar), (n2'.Node.id, n2'.Node.find, n2'.Node.ccpar))]))
                  dag.stack;
                Node.merge n1 n2;
                is_theory_consistent dag
            end
          | Not (Eq(e1,e2)) ->
            begin
              let n1 = get_node dag e1 in
              let n2 = get_node dag e2 in
                dag.neqs <- (n1.Node.id, n2.Node.id) :: dag.neqs;
                Stack.push (StackSat (pred, [ImplyNotEqual (n1.Node.id, n2.Node.id)])) dag.stack;
                (*is_sat dag*)
                (Node.find n1).Node.id <> (Node.find n2).Node.id
            end
          | Atom (Internal _) | Not (Atom (Internal _)) ->
            begin
              Stack.push (StackSat (pred, [])) dag.stack;
              true
            end
          | _ -> failwith "TODO: more theories"
        end

    let pop dag =
      let undo (id, find, parent) =
        let n = get dag id in
          n.Node.find <- find;
          n.Node.ccpar <- parent
      in
      let undo_change c = match c with
        | Equal (old1,old2) ->
          undo old1;
          undo old2
        | ImplyNotEqual (id1, id2) ->
          let (id1', id2') = List.hd dag.neqs in
          let t = List.tl dag.neqs in
            assert (Global.is_off_assert() || (id1 = id1' && id2 = id2'));
            dag.neqs <- t
        | SentToTheory (th, pred) -> failwith "TODO"
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
                  Message.print Message.Debug (lazy("CoreSolver: pop StackInternal"));
                  (get dag id).Node.find <- find;
                  process ()
                end
              | StackSat (pred, sat_changes) -> (* predicate given by sat solver *)
                begin
                  Message.print Message.Debug (lazy("CoreSolver: pop StackSat " ^ (AstUtil.print_pred pred)));
                  List.iter undo_change sat_changes
                end
              | StackTDeduction (pred, theory, old1, old2) ->
                begin
                  Message.print Message.Debug (lazy("CoreSolver: pop StackTDeduction " ^ (AstUtil.print_pred pred)));
                  assert (Global.is_off_assert() || theory = EUF);
                  undo old1;
                  undo old2;
                  process ()
                end
          end
      in
        process ()

    let euf_t_deductions dag =
      let rec inspect_stack () =
        if Stack.is_empty dag.stack then []
        else
          begin
            let t = Stack.pop dag.stack in
            let ans = match t with
              | StackTDeduction (t_eq, EUF, _, _) -> t_eq :: (inspect_stack ())
              | _ -> inspect_stack ()
            in
              Stack.push t dag.stack;
              ans
          end
      in
        inspect_stack ()

    let euf_lemma_with_info dag =
      let (c1,c2) = try
          List.find
            (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
            dag.neqs
        with Not_found ->
          failwith "CoreSolver, euf_lemma_with_info: system is sat!"
      in
      (* raw_core contains only given equalities
       * it is an overapproximation ...
       * find which congruences are needed
       * TODO improve -> do a search for eq paths that makes the contradiction possible
       *)
      let given1, congr1 = Node.get_find_predicates (Node.find (get dag c1)) in
      let given2, congr2 = Node.get_find_predicates (Node.find (get dag c2)) in
      let raw_congruences = euf_t_deductions dag in
      let all_congruences = List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty raw_congruences in
      let needed_congruences = PredSet.inter all_congruences (PredSet.union congr1 congr2) in
      let congruences = List.filter (fun x -> PredSet.mem x needed_congruences) raw_congruences in (*keep congruence in order*)
      let info = List.map (fun x -> (x,EUF)) congruences in
      let contradiction = AstUtil.order_eq (Not (Eq ((get dag c1).Node.expr,(get dag c2).Node.expr))) in
      let raw_core = PredSet.union given1 given2 in
      let core = contradiction :: (PredSet.elements raw_core) in
        (And core, contradiction, EUF, info)

    (* blocking clause *)
    let theory_lemma t = euf_lemma_with_info t

    let rec to_theory_solver t lst = match lst with
      | x::xs ->
        begin
          if push t x then to_theory_solver t xs
          else
            begin
              List.iter (fun _ -> t.sat_solver#pop) xs;
              false
            end
        end
      | [] -> true

    (** Conjunction to blocking clause *)
    let reverse formula = match formula with
      | And lst -> Or (List.map AstUtil.contra lst)
      | Or lst -> failwith ("satPL: reverse expect a conj, found"^(AstUtil.print (Or lst)))
      | e -> Or [AstUtil.contra e] (*abstract can return atoms*)

    type solved = Sat of predicate list
                | Unsat of CsisatDpllProof.res_proof * (predicate * theory * (predicate * theory) list) PredMap.t

    let rec solve t =
      Message.print Message.Debug (lazy("CoreSolver: solving"));
      let rec t_contradiction () =
        Message.print Message.Debug (lazy("CoreSolver: solving t_contradiction"));
        let (new_clause, contradiction, th, explanation) = theory_lemma t in
        let new_clause = reverse new_clause in
        let old_dl = t.sat_solver#get_decision_level in
          assert (Global.is_off_assert() || th = EUF);
          t.explanations <- PredMap.add new_clause (contradiction, th, explanation) t.explanations;
          t.sat_solver#add_clause new_clause;
          let new_dl = t.sat_solver#get_decision_level in
            backjump (old_dl - new_dl)
      and backjump howmany =
          Message.print Message.Debug (lazy("CoreSolver: solving backjump "^(string_of_int howmany)));
          List.iter (fun _ -> pop t) (Utils.range 0 howmany);
          sat_solve ()
      and sat_solve () =
        Message.print Message.Debug (lazy("CoreSolver: solving sat_solve"));
        match t.sat_solver#next with
        | Dpll.Affected lst ->
            if to_theory_solver t lst
            then sat_solve ()
          else t_contradiction ()
        | Dpll.Affectation (lst1,lst2) ->
            if to_theory_solver t lst1
            then Sat (List.filter (fun x -> x <> True) (List.map AstUtil.remove_equisat_atoms lst2))
            else t_contradiction();
        | Dpll.Backtracked howmany -> backjump howmany
        | Dpll.Proof proof ->
          begin
            match proof with
            | Some prf -> Unsat (prf, t.explanations)
            | None -> failwith "expecting a proof"
          end
      in
      if is_consistent t then
        begin
          if is_sat t
          then Sat t.sat_solver#get_solution
          else sat_solve ()
        end
      else
        begin
          if is_theory_consistent t
          then sat_solve ()
          else t_contradiction ()
        end
  end

