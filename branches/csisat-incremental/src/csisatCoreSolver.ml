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

open    CsisatAst
open    CsisatAstUtil
open    CsisatUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module IntSet  = CsisatUtils.IntSet
module OrdSet  = CsisatOrdSet
module EqDag   = CsisatDag
module Dpll    = CsisatDpllCore
module DpllProof = CsisatDpllProof
module SatDL   = CsisatSatDL
(**/**)


(** The different changes that can happen in the system *)
type find_t =  Leader of UndirectedIntGraph.t * PredSet.t (*graph of predicate used to make that CC, and the congruences*)
            |  Member of int (*representative is int*)
type node_info = int * find_t * IntSet.t (* (id, find, ccpar) *)
type euf_change = Deduction of predicate * node_info * node_info * (int list list) (* congruence. last part is a proof (for each argument, a path of equal terms) *)
                | Internal of (int * find_t) list (* path compression: (id, old find) list *)
                | Equal of node_info * node_info (* information to restore previous state *)
                | NotEqual of (int * int) (* for instance a < b ==> ~(a = b) *)
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
      find = Leader (UndirectedIntGraph.empty, PredSet.empty);
      ccpar = IntSet.empty;
    }
    
    (*val copy: t -> t*)
    let copy n stack = {
      id = n.id;
      fn = n.fn;
      args = n.args;
      arity = n.arity;
      expr = n.expr;
      nodes = n.nodes;
      events = stack;
      find = n.find;
      ccpar = n.ccpar;
    }

    let to_string n =
      "node "^(string_of_int n.id)^
      " ("^(print_expr n.expr)^") "^
      n.fn^"("^(String.concat ", "(List.map string_of_int n.args))^") "^
      " ccpar = {"^(String.concat ", " (List.map string_of_int (IntSet.elements n.ccpar)))^"}"


    let set_ccparent node set = node.ccpar <- set
    let add_ccparent node n = node.ccpar <- (IntSet.add n node.ccpar)
    let get_ccparent node = node.ccpar

    
    (*val find: t -> t*)
    let rec find this =
      let path_compression = ref [] in
      let rec process this = match this.find with
        | Leader _ -> this
        | Member id ->
          begin
            let top = find (this.nodes.(id)) in
              if top.id <> id then
                begin
                  path_compression := (this.id, this.find) :: !path_compression;
                  this.find <- Member top.id
                end;
              top
          end
      in
      let result = process this in
        if !path_compression <> [] then
          Stack.push (Internal !path_compression) (this.events);
        result

    let get_find_predicates_find f = match f with
      | Leader (g,p) -> (g,p)
      | Member _ -> failwith "get_find_predicates: only for leaders"
    let get_find_predicates n = get_find_predicates_find n.find


    (*val union: t -> t -> (t * t)*)
    let union congruence this that given_this given_that = 
      let n1 = find this in
      let n2 = find that in
      let gr1, c1 = get_find_predicates n1 in
      let gr2, c2 = get_find_predicates n2 in
      let new_gr = UndirectedIntGraph.add (UndirectedIntGraph.merge gr1 gr2) given_this.id given_that.id in
      let new_c = maybe (fun x -> PredSet.add x (PredSet.union c1 c2)) (lazy (PredSet.union c1 c2)) congruence in
        n2.find <- Leader (new_gr, new_c);
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

    let mk_eq a b = order_eq (Eq (a.expr, b.expr))

    (*val merge: t -> t -> unit*)
    let merge this that =
      (* report only congruences *)
      let first_to_stack _ _ _ _ =
        Message.print Message.Debug (lazy("SatEUF: merge given " ^ (print_pred (mk_eq this that))));
      in
      let other_to_stack a b changed_a changed_b =
        Message.print Message.Debug (lazy("SatEUF: merge congruence " ^ (print_pred (mk_eq a b))));
        let args_equalities =
          List.map
            (fun (arg_a, arg_b) ->
              let graph, _ = get_find_predicates (find this.nodes.(arg_a)) in
                UndirectedIntGraph.shortest_path graph arg_a arg_b
            )
            (List.combine a.args b.args)
        in
        let stack_elt =
          Deduction
            (mk_eq a b,
            (changed_a.id, changed_a.find, changed_a.ccpar),
            (changed_b.id, changed_b.find, changed_b.ccpar),
            args_equalities)
        in
          Stack.push stack_elt a.events
      in
      let rec process to_stack congruence this that =
        let n1 = find this in
        let n2 = find that in
          if n1.id <> n2.id then
            begin
              let p1 = ccpar n1 in
              let p2 = ccpar n2 in
              let to_test = cartesian_product (IntSet.elements p1) (IntSet.elements p2) in
                to_stack this that n1 n2; (* report changes *)
                union congruence n1 n2 this that;
                  Message.print Message.Debug (lazy(
                    "SatEUF: merge to_test " ^
                    (String.concat ", "
                      (List.map
                        (fun (x,y) -> print_pred (mk_eq this.nodes.(x) this.nodes.(y)))
                        to_test))));
                List.iter
                  (fun (x,y) ->
                    let x = this.nodes.(x) in
                    let y = this.nodes.(y) in
                      if (find x).id <> (find y).id && congruent x y then
                        process other_to_stack (Some (mk_eq x y)) x y
                  )
                  to_test
          end
        else
          Message.print Message.Debug (lazy("SatEUF: merge alreay equal " ^ (print_pred (mk_eq this that))))
      in
        process first_to_stack None this that 
  end

module SatEUF =
  struct
    type t = {
      nodes: Node.t array;
      expr_to_node: Node.t ExprMap.t;
      stack: euf_change Stack.t;
      mutable neqs: (int * int) list; (* neqs as pairs of node id *)
    }
    
    let to_string dag =
      let buffer = Buffer.create 1000 in
      let add = Buffer.add_string buffer in
        add "SatEUF:\n";
        Array.iter (fun x -> add (Node.to_string x); add "\n") dag.nodes;
        Buffer.contents buffer

    let get dag i = dag.nodes.(i)
    let get_node dag expr = ExprMap.find expr dag.expr_to_node
    let get_node_info dag i =
      let n = get dag i in
        (n.Node.id, n.Node.find, n.Node.ccpar)

    (* restore some node_info *)
    let undo dag (id, find, parent) =
      let n = get dag id in
        n.Node.find <- find;
        n.Node.ccpar <- parent

    let is_sat dag =
      not (
        List.exists
          (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
          dag.neqs
      )
    
    (*test if two terms are equal*)
    let entailed t pred = match pred with
      | Eq (e1, e2) ->
        begin
          let n1 = get_node t e1 in
          let n2 = get_node t e2 in
          let n1' = Node.find n1 in
          let n2' = Node.find n2 in
          let res = n1'.Node.id = n2'.Node.id in
            Message.print Message.Debug (lazy("SatEUF: entailed " ^ (print_pred pred) ^ " -> " ^ (string_of_bool res)));
            res
        end
      (*TODO Neq*)
      | err -> failwith ("SatEUF, entailed only eq for the moment ("^(print_pred pred)^")")

    let t_deductions dag =
      let rec inspect_stack () =
        if Stack.is_empty dag.stack then []
        else
          begin
            let t = Stack.pop dag.stack in
            let ans = match t with
              | Deduction (t_eq, _, _, _) -> t_eq :: (inspect_stack ())
              | _ -> inspect_stack ()
            in
              Stack.push t dag.stack;
              ans
          end
      in
        inspect_stack ()


    (* justify a congruence, return given preds + sub-congruences
     * for each congruences take the justification from the stack.
     * the congruences are loosely ordered (new to old DFS).
     *)
    let justify_congruence t pred =
      Message.print Message.Debug (lazy("SatEUF: justify_congruence for " ^ (print_pred pred)));
      let info = ref [] in
      let congruences = ref PredMap.empty in
        Stack.iter
          (fun s -> match s with
            | Deduction (t_eq, _, _, proof) -> congruences := PredMap.add t_eq proof !congruences
            | _ -> ()
          )
          t.stack;
        let rec process given_preds to_justify =
          if PredSet.is_empty to_justify then given_preds
          else
            begin
              let pred = PredSet.choose to_justify in
              let proof = List.flatten (List.map path_to_edges (PredMap.find pred !congruences)) in
              let preds = List.map (fun (a,b) -> Node.mk_eq (get t a) (get t b)) proof in
              let congruences, givens = List.partition (fun p -> PredMap.mem p !congruences) preds in
              let new_given = List.fold_left (fun acc x -> PredSet.add x acc) given_preds givens in
              let new_to_justify = List.fold_left (fun acc x -> PredSet.add x acc) (PredSet.remove pred to_justify) congruences in
                Message.print Message.Debug (lazy("SatEUF: justified " ^ (print_pred pred)));
                info := pred :: !info;
                process new_given new_to_justify
            end
        in
        let pred_set = process PredSet.empty (PredSet.singleton pred) in
          (PredSet.elements pred_set, List.rev !info)

    (* TODO mk_lemma should return the 'proof' of an equality (congruence or not) using only elements.
     * find the shortest path, identify which predicates are congruences,
     * for each congruences take the justification from the stack.
     *)
    let mk_lemma dag n1 n2 (graph, congr) =
      Message.print Message.Debug (lazy("SatEUF: mk_lemma for " ^ (print_pred (Node.mk_eq n1 n2))));
      let path = UndirectedIntGraph.shortest_path graph n1.Node.id n2.Node.id in
      let edges = path_to_edges path in
      let all_preds =
        List.fold_left
          (fun acc (a,b) ->
            let node_a = get dag a in
            let node_b = get dag b in
              PredSet.add (Node.mk_eq node_a node_b) acc)
          PredSet.empty
          edges
      in
      let raw_congruences = t_deductions dag in
      let all_congruences = List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty raw_congruences in
      let needed_congruences = PredSet.inter all_congruences all_preds in
      let given = PredSet.diff all_preds needed_congruences in
      let preds_info = List.map (justify_congruence dag) (PredSet.elements needed_congruences) in
      let preds, infos = List.split preds_info in
      let core_set = List.fold_left (fun acc x -> PredSet.add x acc) given (List.flatten preds) in
      let all_needed_congruence = List.fold_left (fun acc x -> PredSet.add x acc) needed_congruences (List.flatten infos) in
      let ordered_info = List.filter (fun x -> PredSet.mem x all_needed_congruence) raw_congruences in
        Message.print Message.Debug (lazy("SatEUF: all_preds = " ^ (String.concat ", " (List.map print_pred (PredSet.elements all_preds)))));
        Message.print Message.Debug (lazy("SatEUF: all_congruences = " ^ (String.concat ", " (List.map print_pred raw_congruences))));
        Message.print Message.Debug (lazy("SatEUF: needed_congruences = " ^ (String.concat ", " (List.map print_pred (PredSet.elements needed_congruences)))));
        Message.print Message.Debug (lazy("SatEUF: given = " ^ (String.concat ", " (List.map print_pred (PredSet.elements given)))));
        (And (PredSet.elements core_set), List.map (fun x -> (x,EUF)) ordered_info)

    let lemma_with_info_for dag (c1, c2) =
      let n1 = (get dag c1) in
      let n2 = (get dag c2) in
      let find = Node.get_find_predicates (Node.find n1) in
        assert((Node.find n1).Node.id = (Node.find n2).Node.id);
        mk_lemma dag n1 n2 find

    (* core => Not contradiction *)
    let justify t pred =
      let (e1, e2, contradiction) = match pred with
        | Eq(e1,e2) | Not (Eq(e1,e2)) -> (e1, e2, Not (Eq (e1,e2)))
        | _ -> failwith "SatEUF, justify is only for EQ or NEQ"
      in
      let id1 = (get_node t e1).Node.id in
      let id2 = (get_node t e2).Node.id in
      let (core, info) = lemma_with_info_for t (id1, id2) in
        (core, contradiction, EUF, info)
    
    let lemma_with_info dag =
      let (c1,c2) = try
          List.find
            (fun (id1,id2) -> (Node.find (get dag id1)).Node.id = (Node.find (get dag id2)).Node.id)
            dag.neqs
        with Not_found ->
          failwith "SatEUF, lemma_with_info: system is sat!"
      in
      let n1 = (get dag c1) in
      let n2 = (get dag c2) in
        justify dag (Node.mk_eq n1 n2)

    (* for NO EQ propagation, use an undo/redo system
     * TODO needs to remember which congruence is responsible for an eq *)
    let propagations dag shared =
      Message.print Message.Debug (lazy("SatEUF: propagations on " ^ (String.concat "," (List.map print_expr shared))));
      let rec to_last_deduction () =
        if Stack.is_empty dag.stack then None
        else
          begin
            match Stack.pop dag.stack with
            | (Deduction (_, (id1, f1, c1), (id2, f2, c2), _)) as top ->
              begin
                let old1 = (id1, f1, c1) in
                let old2 = (id2, f2, c2) in
                let current1 = get_node_info dag id1 in
                let current2 = get_node_info dag id2 in
                  undo dag old1;
                  undo dag old2;
                  Some (top, current1, current2)
              end
            | Internal lst ->
              begin
                List.iter (fun (id, find) -> (get dag id).Node.find <- find) lst;
                to_last_deduction ()
              end
            | top ->
              begin
                Stack.push top dag.stack;
                None
              end
         end
      in
      let are_equal exprs_pairs =
        List.filter
          (fun (a,b) ->
            (Node.find (get dag a)).Node.id = (Node.find (get dag b)).Node.id
          )
          exprs_pairs
      in
      let all_equals =
        let to_test = cartesian_product shared shared in
        let as_nodes = List.map (fun (a, b) -> ((get_node dag a).Node.id, (get_node dag b).Node.id)) to_test in
        let equals = List.filter (fun (a,b) -> a < b ) as_nodes in
          are_equal equals
      in
      (*determines which thing are equal now because of the new congruences (newer to older)*)
      let rec new_equalities equals =
        match to_last_deduction () with
        | Some (top, restore1, restore2) ->
          begin
            (*TODO rewrite that part *)
            let old_equals = are_equal equals in
            let new_equals = List.filter (fun x -> not (List.mem x old_equals)) equals in
            (*prune using cc from old_equals*)
            let old_cc = get_scc_undirected_graph old_equals in
            let node_to_cc = Hashtbl.create (List.length shared) in
              List.iter
                (fun cc ->
                  let representative = List.hd cc in
                    List.iter (fun x -> Hashtbl.add node_to_cc x representative) cc
                )
                old_cc;
              let get_representative = Hashtbl.find node_to_cc in
              let new_equals_pruned =
                let replaced =
                  List.map
                    (fun (a,b) ->
                      let rep_a = get_representative a in
                      let rep_b = get_representative b in
                        if rep_a <= rep_b then (rep_a, rep_b) else (rep_b, rep_a)
                    )
                    new_equals
                in
                  OrdSet.list_to_ordSet replaced
              in
              let recurse = new_equalities old_equals in
                (* restore previous status *)
                undo dag restore1;
                undo dag restore2;
                Stack.push top dag.stack;
                new_equals_pruned :: recurse
          end
        | None -> []
      in
      let deductions = List.flatten (new_equalities all_equals) in
        List.map (fun (a,b) -> order_eq (Eq ((get dag a).Node.expr, (get dag b).Node.expr))) deductions

    let create pred =
      let set = get_expr_deep_set pred in
      let id = ref 0 in
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
          nodes = nodes;
          expr_to_node = !expr_to_node;
          stack = stack;
          neqs = []
        }
      in
        Message.print Message.Debug (lazy("SatEUF, " ^ (to_string graph)));
        graph

    let push t pred =
      Message.print Message.Debug (lazy("SatEUF: push " ^ (print_pred pred)));
      match pred with
      | Not (Eq (e1,e2)) ->
        begin
          let n1 = get_node t e1 in
          let n2 = get_node t e2 in
          let neq = (n1.Node.id, n2.Node.id) in
            t.neqs <- neq :: t.neqs;
            Stack.push (NotEqual neq) t.stack;
            (Node.find n1).Node.id <> (Node.find n2).Node.id
        end
      | Eq (e1, e2) ->
        begin
          let n1 = get_node t e1 in
          let n2 = get_node t e2 in
          let n1' = Node.find n1 in
          let n2' = Node.find n2 in
          let change = Equal (get_node_info t n1'.Node.id, get_node_info t n2'.Node.id) in
            Stack.push change t.stack;
            Node.merge n1 n2;
            is_sat t
        end
      | _ -> failwith "SatEUF: only Eq, Not Eq"

    let pop t =
      Message.print Message.Debug (lazy("SatEUF: pop"));
      let rec process () =
        if Stack.is_empty t.stack then
          failwith "SatEUF: pop called on an empty stack"
        else
          begin
            match Stack.pop t.stack with
            | Internal lst ->
              begin
                Message.print Message.Debug (lazy("SatEUF: pop StackInternal"));
                List.iter (fun (id, find) -> (get t id).Node.find <- find) lst;
                process ()
              end
            | Deduction (pred, old1, old2, _) ->
              begin
                Message.print Message.Debug (lazy("SatEUF: pop StackEUFDeduction " ^ (print_pred pred)));
                undo t old1;
                undo t old2;
                process ()
              end
            | Equal (old1, old2) ->
              begin
                Message.print Message.Debug (lazy("SatEUF: pop Equal"));
                undo t old1;
                undo t old2
              end
            | NotEqual (i1, i2) ->
              begin
                Message.print Message.Debug (lazy("SatEUF: pop NotEqual"));
                let (i1', i2') = List.hd t.neqs in
                  assert(i1 = i1' && i2 = i2');
                  t.neqs <- List.tl t.neqs
              end
        end
      in
        process ()
  end

module CoreSolver =
  struct

    type change = StackSat of predicate (* predicate given by sat solver *)
                | StackNO of predicate * theory
                | StackChanges of (theory * predicate) list (*what was sent to which theory*)

    type t = {
      sat_solver: Dpll.csi_dpll;
      propositions: PredSet.t;
      stack: change Stack.t;
      mutable explanations: (predicate * theory * (predicate * theory) list) PredMap.t;
      (* TODO what is needed for the theory splitting and theory solvers *)
      (* a theory solver being a module, there are some problem
       * Functors: modular, but only handles a fixed number of solver
       * class: modular, dynamic dispatch
       * explicitely listing all possible solver: not modular, but can take advantage of the specificties of each theories.
       *)
      shared: expression OrdSet.t;
      definitions: expression ExprMap.t;
      rev_definitions: expression ExprMap.t;
      euf: SatEUF.t;
      dl: SatDL.t
    }

    (* EUF *)
    let euf_to_string dag           = SatEUF.to_string dag.euf
    let get dag                     = SatEUF.get dag.euf
    let get_node dag                = SatEUF.get_node dag.euf
    let get_node_info dag           = SatEUF.get_node_info dag.euf
    let undo dag                    = SatEUF.undo dag.euf
    let is_euf_sat dag              = SatEUF.is_sat dag.euf
    let euf_lemma_with_info_for dag = SatEUF.lemma_with_info_for dag.euf
    let euf_lemma_with_info dag     = SatEUF.lemma_with_info dag.euf
    let euf_justify dag             = SatEUF.justify dag.euf
    let euf_propagations dag        = SatEUF.propagations dag.euf
    (* end of EUF *)

    (* DL *)
    let dl_lemma_with_info_for t pred = SatDL.justify t.dl pred
    let dl_lemma_with_info t = SatDL.unsat_core_with_info t.dl
    let is_dl_sat t = SatDL.is_sat t.dl
    (* end of DL *)

    let is_theory_consistent t =
          is_euf_sat t
      &&  is_dl_sat t

    (* has a satisfiable assignement *)
    let is_sat t = t.sat_solver#is_sat && is_theory_consistent t

    (* partially sat / no explicit contradiction *)
    let is_consistent t = t.sat_solver#is_consistent && is_theory_consistent t

    let add_and_test_dl t pred =
      Message.print Message.Debug (lazy("CoreSolver: add_and_test_dl " ^ (print_pred pred)));
      try
        let dl_consistent = SatDL.push t.dl pred in
          Some (dl_consistent, (DL, pred))
      with Failure str ->
        begin
          if Str.string_match (Str.regexp "^SatDL, expected DL expression:") str 0
          then None
          else failwith str
        end
        | Not_found -> None

    let add_and_test_euf t pred =
      Message.print Message.Debug (lazy("CoreSolver: add_and_test_euf " ^ (print_pred pred)));
      try Some(SatEUF.push t.euf pred, (EUF, pred))
      with Not_found -> None

    let undo_change t (th, pred) = match th with
      | DL -> SatDL.pop t.dl
      | EUF -> SatEUF.pop t.euf
      | LA -> failwith "CoreSolver: SentToTheory LA"
    let undo_changes dag lst = List.iter (undo_change dag) lst
    
    (* this is shady business with the order of events (StackInternal) and the pop/undo *)
    let rec insert_changes dag changes = match Stack.top dag.stack with
      | StackNO _ | StackSat _ -> Stack.push changes dag.stack
      | _ ->
        begin
          let t = Stack.pop dag.stack in
            insert_changes dag changes;
            Stack.push t dag.stack
        end


    let rec propagate t sat =
      Message.print Message.Debug (lazy("CoreSolver: NO ("^(string_of_bool sat)^")"));
      (* ask EUF for new EQ *)
      let euf_deductions = euf_propagations t t.shared in
      let euf_deductions = List.filter (fun x -> not (SatDL.entailed t.dl x)) euf_deductions in
      (* ask DL for new EQ *)
      let dl_deductions = SatDL.propagations t.dl t.shared in
      let dl_deductions = List.filter (fun x -> not (SatEUF.entailed t.euf x)) dl_deductions in
      (* Nelson Oppen: *)
      let t1_to_t2 th1 fct2 lst acc =
        List.fold_left
          (fun sat pred ->
            if sat then
              begin
                (*push on stack first *)
                Stack.push (StackNO (pred, th1)) t.stack;
                match fct2 pred with
                | Some (sat, change) ->
                  begin
                    insert_changes t (StackChanges [change]);
                    sat
                  end
                | None -> failwith "CoreSolver: shared variables not shared ?!"
              end
            else
              false
          )
          acc
          lst
      in
      (* first DL -> EUF *)
      let dl_to_euf = t1_to_t2 DL (add_and_test_euf t) dl_deductions sat in
      (* then EUF -> DL *)
      let euf_to_dl = t1_to_t2 EUF (add_and_test_dl t) euf_deductions dl_to_euf in
        (* if there was some propagation -> rec call *)
        if euf_to_dl && (dl_deductions <> [] || euf_deductions <> [])
        then propagate t euf_to_dl
        else euf_to_dl

    (*TODO make code cleaner with 'maybe' *)
    (* push with ot without purfying the terms *)
    let push_abs dag pred abstract =
      (* abstract pred since it did not get through the theory split *)
      let pred' = if abstract then put_theory_split_variables dag.rev_definitions pred else pred in
      (*TODO other theories *)
      Message.print Message.Debug (lazy("CoreSolver: push " ^ (print_pred pred)));
      if not (is_theory_consistent dag) then failwith "CoreSolver: push called on an already unsat system."
      else
        begin
          (*push on stack first *)
          Stack.push (StackSat pred) dag.stack;
          match pred' with
          | Eq _ ->
            begin
              let res, changes = maybe (fun (a, b) -> (a, [b])) (lazy (true, [])) (add_and_test_euf dag pred') in
              let res', changes' =
                if res then maybe (fun (a, b) -> (a, b :: changes)) (lazy (res, changes)) (add_and_test_dl dag pred')
                else res, changes
              in
                assert(changes' <> []);
                insert_changes dag (StackChanges changes');
                (*NO*)
                propagate dag res'
            end
          | Not (Eq _) ->
            begin
              match add_and_test_euf dag pred' with
              | Some (status, changed) ->
                insert_changes dag (StackChanges [changed]);
                status
              | None -> failwith "CoreSolver: NEQ not found"
            end
          | Atom (CsisatAst.Internal _) | Not (Atom (CsisatAst.Internal _)) -> true
          | Leq (_, _) ->
            begin
              let dl_consistent, dl_change =
                match add_and_test_dl dag pred' with
                | Some (res, chg) -> (res, chg)
                | None -> failwith "CoreSolver: Leq not in DL ??"
              in
                insert_changes dag (StackChanges [dl_change]);
                (*NO*)
                propagate dag dl_consistent
            end
          | Lt (e1, e2) ->
            begin
              (*implies not EQ*)
              let (res, changes) = maybe (fun (a,b) -> (a,[b])) (lazy (true, [])) (add_and_test_euf dag (Not (Eq (e1, e2)))) in
              let res', changes' =
                if res then
                  maybe
                    (fun (a,b) -> (a, b::changes))
                    (lazy (failwith "CoreSolver: Lt not in DL ??"))
                    (add_and_test_dl dag pred')
                else
                  (res, changes)
              in
                insert_changes dag (StackChanges changes');
                (*NO*)
                propagate dag res'
            end
          | _ -> failwith "TODO: more theories"
        end
    (* purify and push *)
    let push dag pred = push_abs dag pred true

    let pop dag =
      let rec process () =
        if Stack.is_empty dag.stack then
          failwith "CoreSolver: pop called on an empty stack"
        else
          begin
            let t = Stack.pop dag.stack in
              match t with
              | StackSat pred -> (* predicate given by sat solver *)
                begin
                  Message.print Message.Debug (lazy("CoreSolver: pop StackSat " ^ (print_pred pred)))
                end
              | StackChanges sat_changes ->
                begin
                  Message.print Message.Debug (lazy("CoreSolver: pop StackChanges"));
                  undo_changes dag sat_changes;
                  process ()
                end
              | StackNO (pred, th) ->
                begin
                  Message.print Message.Debug (lazy("CoreSolver: pop StackNO " ^ (print_pred pred) ^ " from " ^(string_of_theory th)));
                  process ()
                end
          end
      in
        process ()

    (* blocking clause
     * for the interpolation (later) only the eq (deductions) are needed
     * for the blocking clause, need to 'justify' the deductions
     *)
    let theory_lemma t =
      (* this is more complex, i.e. NO.
       * 1) determine which theory has a contradiction
       * 2) get the core
       * 3) for each NO that appears in the core -> justify (recursively)
       *)
      let justify_pred (pred, th) = match th with
        | EUF ->
          begin
            (*TODO map the deduction to the related congruence.
             * in fact multiple congruences might be needed for one equaliy ...*)
            let congruence = pred in
              euf_justify t congruence
          end
        | DL -> SatDL.justify t.dl pred
        | _ -> failwith "CoreSolver, theory_lemma: more theory"
      in
      let rec justify justified core deduction =
        if PredSet.mem (fst deduction) justified then (justified, core)
        else
          begin
            let (ded_core, npred, _, _) = justify_pred deduction in
              Message.print Message.Debug (lazy("CoreSolver: justification of "^(print_pred (fst deduction))^" is "^(print_pred ded_core)));
            (*must look at ded_core to find further NO *)
            let (no_to_justify, lst) = split_shared_NO ded_core in
            let lst = match ded_core with And lst -> lst | _ -> failwith "CoreSolver, theory_lemma" in
            let core' = List.fold_left (fun acc x -> PredSet.add x acc) core lst in
            let justified' = PredSet.add (fst deduction) justified in
              justify_list justified' core' no_to_justify
          end
      and justify_list justified core lst =
        List.fold_left (fun (a, b) c -> justify a b c) (justified, core) lst
      (* returns the propagated (recent to old) *)
      and split_shared_NO core =
        let core = get_literal_set core in
        let used_no = ref [] in
        let used_pred = ref PredSet.empty in
          Stack.iter
            (fun s -> match s with
              | StackNO (a, b) ->
                if PredSet.mem a core then
                  begin
                    used_no := (a,b) :: !used_no;
                    used_pred := PredSet.add a !used_pred
                  end
              | _ -> ()
            )
            t.stack;
          let nos = List.rev !used_no in
          let rest = PredSet.elements (PredSet.diff core !used_pred) in
            (nos, rest)
      in
      let (core, pred, th, deductions) = 
        match (is_euf_sat t, is_dl_sat t) with
        | (false, _) -> euf_lemma_with_info t
        | (_, false) -> dl_lemma_with_info t
        | _ -> failwith "CoreSolver, theory_lemma: all theories are OK."
      in
      Message.print Message.Debug (lazy("CoreSolver: full core is "^(print_pred core)));
      let (no_to_justify, core) = split_shared_NO (normalize_only (And [pred; core])) in
      Message.print Message.Debug (lazy("CoreSolver: contradiction in "^(string_of_theory th)^" with " ^ (print_pred pred)));
      Message.print Message.Debug (lazy("CoreSolver: given core is "^(print_pred (And core))));
      Message.print Message.Debug (lazy("CoreSolver: deductions are "^(String.concat ", " (List.map (fun (a,b) -> (print_pred a)^"("^(string_of_theory b)^")") deductions))));
      Message.print Message.Debug (lazy("CoreSolver: NO to justify are "^(String.concat ", " (List.map (fun (a,b) -> (print_pred a)^" ("^(string_of_theory b)^")") no_to_justify))));
      let (_, core') = justify_list PredSet.empty PredSet.empty no_to_justify in
      let full_core = normalize (And (core @ (PredSet.elements core'))) in
        (full_core, pred, th, []) (*TODO explanation: needs to accumulate deductions (for later interpolation)*)

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

    (* propagate T deduction to the sat solver *)
    (*TODO NO variable renaming*)
    let t_propagation t =
      let assigned =
        let p = ref PredSet.empty in
          Stack.iter
            (fun c -> match c with
              | StackSat lit ->
                p := PredSet.union (get_proposition_set lit) !p
              | _ -> ()
            )
            t.stack;
          !p
      in
      let classes =
        List.map
          (fun (id1,id2) -> ((Node.find (get t id1)).Node.id, (Node.find (get t id2)).Node.id))
          t.euf.SatEUF.neqs (*TODO encapsulation*)
      in
      let unassigned = PredSet.diff t.propositions assigned in
      let implied =
        map_filter 
          (fun p -> match p with
            | Eq(e1,e2) ->
              begin
                let n1 = get_node t e1 in
                let n2 = get_node t e2 in
                  if (Node.find n1).Node.id = (Node.find n2).Node.id then
                    begin
                      let (core, _) = euf_lemma_with_info_for t (n1.Node.id, n2.Node.id) in
                        Some (Eq(e1,e2), core)
                    end
                  else
                    None
              end
            | Not (Eq(e1,e2)) ->
              begin
                let n1 = get_node t e1 in
                let n2 = get_node t e2 in
                let r1 = Node.find n1 in
                let r2 = Node.find n2 in
                  if   List.mem (r1.Node.id, r2.Node.id) classes
                    || List.mem (r2.Node.id, r1.Node.id) classes
                  then
                    begin
                      (*take the path to the representative on both side ?? not the smallest explanation *)
                      let (core1, _) = euf_lemma_with_info_for t (n1.Node.id, r1.Node.id) in
                      let (core2, _) = euf_lemma_with_info_for t (n2.Node.id, r2.Node.id) in
                      let core = match (core1, core2) with
                        | (And lst1, And lst2) -> normalize_only (And (lst1 @ lst2))
                        | _ -> failwith "..."
                      in
                        Some (Not (Eq(e1,e2)), core)
                    end
                  else None
              end
            | Atom (CsisatAst.Internal _)
            | Not (Atom (CsisatAst.Internal _)) -> None
            | other ->
              begin
                Message.print Message.Error (lazy ("TODO: more theories -> "^(print other)));
                None
              end
          )
          (PredSet.elements unassigned)
      in
        (*TODO adding clauses should not lead to contradictions *)
        implied

    (** Conjunction to blocking clause *)
    let reverse formula = match formula with
      | And lst -> Or (List.map contra lst)
      | Or lst -> failwith ("satPL: reverse expect a conj, found"^(print (Or lst)))
      | e -> Or [contra e] (*abstract can return atoms*)

    type solved = Sat of predicate list
                | Unsat of CsisatDpllProof.res_proof * (predicate * theory * (predicate * theory) list) PredMap.t

    let solved_to_string t = match t with
      | Sat lst -> "Satisfiable: " ^ (String.concat ", " (List.map print_pred lst))
      | Unsat (res, blocking_clauses) ->
        begin
          let (str_prf, (_,index_to_atom, clauses)) = CsisatDpllProof.tracecheck_of_proof_with_tables res in
          let blocking_clause pred (contradiction, th, explanation) =
            (* TODO refactor the 'theory proof' to piggyback more informations *)
            failwith "TODO"
          in
          let prop_buffer = Buffer.create 1000 in
          let clause_buffer = Buffer.create 1000 in
          let blocking_buffer = Buffer.create 1000 in
            Hashtbl.iter (fun k v -> Buffer.add_string prop_buffer ((string_of_int k) ^ " -> " ^ (print_pred v) ^ "\n")) index_to_atom;
            Hashtbl.iter (fun k v -> Buffer.add_string clause_buffer ((string_of_int v) ^ " -> " ^ (print_pred (Or (PredSet.elements k))) ^ "\n")) clauses;
            PredMap.iter (fun k v -> Buffer.add_string blocking_buffer (blocking_clause k v)) blocking_clauses;
            "resolution proof (tracecheck format):\n" ^
            str_prf ^ "\n" ^
            "propositions:\n" ^
            (Buffer.contents prop_buffer) ^
            "clauses:\n" ^
            (Buffer.contents clause_buffer) ^
            "blocking clauses:\n" ^
            (Buffer.contents blocking_buffer)
        end

    let rec solve t =
      Message.print Message.Debug (lazy("CoreSolver: solving"));
      let rec t_contradiction () =
        Message.print Message.Debug (lazy("CoreSolver: solving t_contradiction"));
        let (new_clause, contradiction, th, explanation) = theory_lemma t in
        (*NO variable renaming*)
        (*TODO replacing the right stuff,
         * definitions should no appears in the new clause.
         *)
        let new_clause = normalize (remove_theory_split_variables t.definitions new_clause) in
        let contradiction = normalize (remove_theory_split_variables t.definitions contradiction) in
        let new_clause = reverse new_clause in
        let old_dl = t.sat_solver#get_decision_level in
          t.explanations <- PredMap.add new_clause (contradiction, th, explanation) t.explanations;
          t.sat_solver#add_clause new_clause;
          let new_dl = t.sat_solver#get_decision_level in
            backjump (old_dl - new_dl)
      and backjump howmany =
          Message.print Message.Debug (lazy("CoreSolver: solving backjump "^(string_of_int howmany)));
          List.iter (fun _ -> pop t) (range 0 howmany);
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
            then Sat (List.filter (fun x -> x <> True) (List.map remove_equisat_atoms lst2))
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

    (*TODO split the theories and keep what belongs to what *)
    let create pred =
      let (euf_formula, la_formula, shared, definitions) = split_formula_LI_UIF pred in
      let sat_solver = new Dpll.csi_dpll true in
      let stack = Stack.create () in
      let pset = get_proposition_set pred in
      (*EUF*)
      let euf = SatEUF.create (And euf_formula) in
      (* end of EUF *)
      (* DL *)
      (*TODO check that it really is only DL*)
      (* add the equalities among shared variables => cheaper T-propagation checking *)
      let possible_deduction =
        OrdSet.list_to_ordSet (
          map_filter 
            ( fun (x, y) -> if x <> y then Some (order_eq (Eq (x,y))) else None)
            (cartesian_product shared shared))
      in
      let extended_la_formula = to_conjunctive_list (normalize (And (possible_deduction @ la_formula))) in
      let dl_solver = SatDL.create SatDL.Integer extended_la_formula in
      (* end of DL *)

      let graph = {
          sat_solver = sat_solver;
          propositions = pset;
          stack = stack;
          explanations = PredMap.empty;
          shared = shared;
          definitions = definitions;
          rev_definitions = ExprMap.fold (fun k v acc -> ExprMap.add v k acc) definitions ExprMap.empty;
          euf = euf;
          dl = dl_solver
        }
      in
      let f =
        if is_cnf pred then pred 
        else match equisatisfiable pred with
          | (_,_,f) -> f
      in
      let f = cnf (simplify f) in
        sat_solver#init f;
        (*already push the definitions*)
        ExprMap.iter (fun k v -> assert(push_abs graph (order_eq (Eq (k,v))) false)) graph.definitions;
        Message.print Message.Debug (lazy("CoreSolver: created"));
        Message.print Message.Debug (lazy("EUF = "^(String.concat ", " (List.map print euf_formula))));
        Message.print Message.Debug (lazy("LA  = "^(String.concat ", " (List.map print la_formula))));
        Message.print Message.Debug (lazy("defs= "^(String.concat ", " (ExprMap.fold (fun k v acc -> ((print_expr k)^ "->"^(print_expr v)) :: acc) definitions []))));
        graph

  end

