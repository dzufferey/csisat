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

open    CsisatAst
open    CsisatAstUtil
open    CsisatUtils
(**/**)
module Global  = CsisatGlobal
module Message = CsisatMessage
module IntSet  = CsisatUtils.IntSet
module OrdSet  = CsisatOrdSet
module EqDag   = CsisatDag
(**/**)


(** The different changes that can happen in the system *)
type find_t =  Leader of UndirectedIntGraph.t * PredSet.t (*graph of predicate used to make that CC, and the congruences*)
            |  Member of int (*representative is int*)
type node_info = int * find_t * IntSet.t (* (id, find, ccpar) *)
type euf_change = Deduction of predicate * node_info * node_info * (int list list) (* congruence. last part is a proof (for each argument, a path of equal terms) *)
                | Internal of (int * find_t) list (* path compression: (id, old find) list *)
                | Equal of node_info * node_info (* information to restore previous state *)
                | NotEqual of (int * int) (* for instance a < b ==> ~(a = b) *)


type congruence_proof = Congruence of expression * expression * (congruence_path list) (* last part is, for each argument, a path of equal terms.*)
                      | Eqs of expression list (* equality path of given predicates *)
and congruence_path = congruence_proof list

let proof_get_left_expr prf = match prf with
  | Congruence (l, _, _) -> l
  | Eqs lst -> List.hd lst

let proof_get_right_expr prf = match prf with
  | Congruence (_, r, _) -> r
  | Eqs lst -> List.hd (List.rev lst)

let proof_final_equality p =
  let a = proof_get_left_expr p in
  let b = proof_get_right_expr p in
    order_eq (Eq (a, b))

let rec path_well_formed lst = match lst with
  | a :: b :: xs -> (proof_get_right_expr a = proof_get_left_expr b) && path_well_formed (b :: xs)
  | _ -> true

let compact_path lst =
  let rec process acc lst = match lst with
    | (Eqs lst1) :: (Eqs lst2) :: xs ->
      begin
        assert (List.hd lst2 = List.hd (List.rev lst1));
        process acc ((Eqs (lst1 @ (List.tl lst2))) :: xs)
      end
    | x :: xs -> process (x :: acc) xs
    | [] -> List.rev acc
  in
  let proof = process [] lst in
    assert (path_well_formed proof);
    proof

let path_final_equality path =
  let a = proof_get_left_expr (List.hd path) in
  let b = proof_get_right_expr (List.hd (List.rev path)) in
    order_eq (Eq (a, b))

let rec string_of_proof prf =
  let eq = proof_final_equality prf in
    match prf with
    | Congruence (a,b,args) ->
      "\\inferrule{ "^(String.concat " \\\\ " (List.map string_of_path args))^" }{ "^(print_pred eq)^" }"
    | Eqs lst -> 
      "\\inferrule{ "^String.concat " = " (List.map print_expr lst)^" }{ "^(print_pred eq)^" }"
and string_of_path path = 
  let eq = path_final_equality path in
    "\\inferrule{ "^(String.concat " \\\\ " (List.map string_of_proof path))^" }{ "^(print_pred eq)^" }"

let rec proof_map_expr fct prf = match prf with
  | Congruence (a,b,args) -> Congruence (fct a, fct b, List.map (path_map_expr fct) args)
  | Eqs lst -> Eqs (List.map fct lst)
and path_map_expr fct path = List.map (proof_map_expr fct) path

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
                    "SatEUF: merge to_test (rev) " ^
                    (String.concat ", "
                      (List.rev_map
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

(*make real congruence proof i.e. using the congruence_proof/path type.*)
let mk_proof dag pred =
  Message.print Message.Debug (lazy("SatEUF: mk_proof for " ^ (print_pred pred)));

  let n1, n2 = match pred with
    | Eq (e1, e2) -> ((get_node dag e1), (get_node dag e2))
    | err -> failwith ("SatEUF: mk_proof can only justify Eq (for the moment), not " ^ (print_pred err))
  in

  (* is a congruence or not *)
  let raw_congruences = t_deductions dag in
  let all_congruences = List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty raw_congruences in
  let is_congruence pred = PredSet.mem pred all_congruences in
  
  let mk_pred (a, b) = 
    let node_a = get dag a in
    let node_b = get dag b in
      Node.mk_eq node_a node_b
  in

  let mk_path n1 n2 graph =
    Message.print Message.Debug (lazy("SatEUF: mk_path for " ^ (print_pred (Node.mk_eq n1 n2)) ^ " in"));
    (*Message.print Message.Debug (lazy(UndirectedIntGraph.to_string graph));*)
    let path = UndirectedIntGraph.shortest_path graph n1.Node.id n2.Node.id in
    (*Message.print Message.Debug (lazy("SatEUF: path is " ^ (String.concat ", " (List.map string_of_int path))));*)
    let edges = path_to_edges path in
    let all_preds =
      List.fold_left
        (fun acc (a,b) -> PredSet.add (mk_pred (a, b)) acc)
        PredSet.empty
        edges
    in
    let used_congruences = List.filter (fun x -> PredSet.mem x all_preds) raw_congruences in
      (edges, used_congruences)
  in

  (* raw proof contained in the stack *)
  let stack_deductions =
    let t = Hashtbl.create 100 in
      Stack.iter
        (fun x ->
          match x with
          | Deduction (pred, _, _, proof) -> Hashtbl.add t pred proof
          | _ -> ()
        )
        dag.stack;
      t
  in
  (*TODO cache proof to avoid computing them multiple times*)
  let rec find_justification pred =
    Message.print Message.Debug (lazy("SatEUF: find_justification for " ^ (print_pred pred)));
    match pred with
    | Eq (Application(s, a1), Application(_,a2)) ->
      begin
        let int_prf = Hashtbl.find stack_deductions pred in
        let args_pairs = List.combine a1 a2 in
        let proofs =
          List.map2
            (fun (a1, a2) prf ->
              (*check direction of prf*)
              let prf =
                if (get dag (List.hd prf)).Node.expr = a1
                then prf
                else List.rev prf
              in
              let edges = path_to_edges prf in
              let preds = List.map mk_pred edges in
              (*check for further congruence*)
              let proofs =
                List.map2
                  (fun x (a,b) ->
                    let a = (get dag a).Node.expr in
                    let b = (get dag b).Node.expr in
                      Message.print Message.Debug (lazy("SatEUF: find_justification processing " ^ (print_expr a) ^ " and " ^ (print_expr b)));
                      if is_congruence x
                      then Congruence (a, b, find_justification x)
                      else Eqs [a;b])
                  preds edges
              in
                compact_path proofs
            )
            args_pairs
            int_prf
        in
          proofs
      end
    | other -> failwith ("SatEUF: not a congruence " ^ (print_pred other))
  in
  
  let graph = fst (Node.get_find_predicates (Node.find n1)) in
  let edges, used_congruences = mk_path n1 n2 graph in
  let sub_proofs = List.fold_left (fun acc p -> PredMap.add p (find_justification p) acc) PredMap.empty used_congruences in
  (*put everything together ...*)
  let raw_proof = 
    List.map
      (fun (a,b) ->
        let pred = mk_pred (a,b) in
        let a = (get dag a).Node.expr in
        let b = (get dag b).Node.expr in
          if PredMap.mem pred sub_proofs
          then Congruence (a, b, PredMap.find pred sub_proofs)
          else Eqs [a; b]
      )
      edges
  in
    Message.print Message.Debug (lazy("SatEUF: mk_proof, raw_proof " ^ (string_of_path raw_proof)));
    compact_path raw_proof


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
