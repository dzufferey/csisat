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
module UIGraph = UndirectedIntGraph
(**/**)


(** The different changes that can happen in the system *)
type find_t =  Leader of UIGraph.t * PredSet.t (*graph of predicate used to make that CC, and the congruences*)
            |  Member of int (*representative is int*)
type node_info = int * find_t * IntSet.t (* (id, find, ccpar) *)
type euf_change = Deduction of predicate * node_info * node_info * (int list list) (* congruence. last part is a proof (for each argument, a path of equal terms) *)
                | Internal of (int * find_t) list (* path compression: (id, old find) list *)
                | Equal of predicate * node_info * node_info (* information to restore previous state *)
                | NotEqual of (int * int) (* for instance a < b ==> ~(a = b) *)

module Proof =
  struct
    type t = Congruence of expression * expression * (t list) (* last part is, for each argument, a path of equal terms.*)
           | Eqs of expression list (* equality path of given predicates *)
           | Path of t list (*alternation of Congruence and Eqs*)

    let rec get_left_expr prf = match prf with
      | Congruence (l, _, _) -> l
      | Eqs lst -> List.hd lst
      | Path lst -> get_left_expr (List.hd lst)

    let rec get_right_expr prf = match prf with
      | Congruence (_, r, _) -> r
      | Eqs lst -> List.hd (List.rev lst)
      | Path lst -> get_right_expr (List.hd (List.rev lst))

    let final_equality p =
      let a = get_left_expr p in
      let b = get_right_expr p in
        order_eq (Eq (a, b))

    let rec path_well_formed lst = match lst with
      | a :: b :: xs -> (get_right_expr a = get_left_expr b) && path_well_formed (b :: xs)
      | _ -> true

    let compact_path proof =
      let rec process acc lst = match lst with
        | (Path lst) :: xs -> process acc (lst @ xs)
        | (Eqs lst1) :: (Eqs lst2) :: xs ->
          begin
            assert (List.hd lst2 = List.hd (List.rev lst1));
            process acc ((Eqs (lst1 @ (List.tl lst2))) :: xs)
          end
        | x :: xs -> process (x :: acc) xs
        | [] -> List.rev acc
      in
      let proof = process [] [proof] in
        assert (path_well_formed proof);
        if List.length proof = 1
        then List.hd proof
        else Path proof

    (** take a proof of a = b && b = c, and return a = c*)
    let append prf1 prf2 =
      assert((get_right_expr prf1) = (get_left_expr prf2));
      compact_path (Path [prf1;prf2])

    let rec to_string prf =
      let eq = final_equality prf in
        match prf with
        | Congruence (a,b,args) ->
          "\\inferrule{ "^(String.concat " \\\\ " (List.map to_string args))^" }{ "^(print_pred eq)^" }"
        | Eqs lst -> 
          "\\inferrule{ "^String.concat " = " (List.map print_expr lst)^" }{ "^(print_pred eq)^" }"
        | Path lst ->
          "\\inferrule{ "^(String.concat " \\\\ " (List.map to_string lst))^" }{ "^(print_pred eq)^" }"

    let rec proof_map_expr fct prf = match prf with
      | Congruence (a,b,args) -> Congruence (fct a, fct b, List.map (proof_map_expr fct) args)
      | Eqs lst -> Eqs (List.map fct lst)
      | Path lst -> Path (List.map (proof_map_expr fct) lst)

    (** returns all the congruence in the proof *)
    let rec proof_congruences_contained prf = match prf with
      | Congruence (a,b,args) ->
        List.fold_left (fun acc x -> PredSet.union (proof_congruences_contained x) acc)
          (PredSet.singleton (order_eq (Eq (a, b))))
          args
      | Eqs _ -> PredSet.empty
      | Path lst ->
        List.fold_left (fun acc x -> PredSet.union (proof_congruences_contained x) acc)
          PredSet.empty
          lst

    (** returns all the given equalities in the proof *)
    let rec proof_equalities_contained prf = match prf with
      | Congruence (a,b,args) ->
        List.fold_left (fun acc x -> PredSet.union (proof_equalities_contained x) acc)
          PredSet.empty
          args
      | Eqs lst ->
        let lst2 = path_to_edges lst in
          List.fold_left (fun acc (a,b) -> PredSet.add (order_eq (Eq (a, b))) acc) PredSet.empty lst2
      | Path lst ->
        List.fold_left (fun acc x -> PredSet.union (proof_equalities_contained x) acc)
          PredSet.empty
          lst

    (* helper for contains: no rec means do not go inside congruence*)
    let rec contains_1expr_no_rec prf e = match prf with
      | Congruence (e1,e2,_) -> e = e1 || e = e2
      | Eqs lst -> List.mem e lst
      | Path lst -> List.exists (fun p -> contains_1expr_no_rec p e) lst

    (* helper for contains: e1 e2 must appear on the same path *)
    let rec contains_2expr prf e1 e2 = match prf with
      | Congruence (e1',e2',lst) ->
        ((e1 = e1' || e1 = e2') && (e2 = e1' || e2 = e2')) ||
        List.exists (fun p -> contains_2expr p e1 e2) lst
      | Eqs lst -> List.mem e1 lst && List.mem e2 lst
      | Path lst ->
        List.exists (fun p -> contains_2expr p e1 e2) lst ||
        (  List.exists (fun p -> contains_1expr_no_rec p e1) lst
        && List.exists (fun p -> contains_1expr_no_rec p e2) lst)

    let contains prf pred = match pred with
      | Eq (e1, e2) -> contains_2expr prf e1 e2
      | _ -> false

    let rec find_terms_in proof (belongs_to: expression -> Interval.t) (where: Interval.t) = match proof with
      | Congruence (e1,e2,lst) ->
        begin
          let args = List.map (fun p -> find_terms_in p belongs_to where) lst in
            match e1 with
            | Application(f, _) -> Application(f, args)
            | _ -> failwith "SatEUF.Proof.find_terms_in: congruence not on Application ??"
        end
      | Eqs lst -> List.find (fun e -> (belongs_to e) = where) lst
      | Path lst ->
        begin
          let candidate =
            List.find
              (fun p -> try ignore(find_terms_in p belongs_to where); true with Not_found -> false)
              lst
          in
            find_terms_in candidate belongs_to where
        end

    (* helper for make_proof_local *)
    let common e1 e2 belongs_to =
      not (Interval.is_empty (Interval.inter (belongs_to e1) (belongs_to e2)))

    (* helper for make_proof_local *)
    let extract_relevant_part a b prf = match prf with
      | Congruence (e1,e2,lst) ->
        begin
          assert(a = e1 && b = e2);
          Congruence (e1,e2,lst)
        end
      | Eqs lst ->
        begin
          assert(List.mem a lst);
          assert(List.mem b lst);
          let start_with_a = drop_while (fun x -> x <> a) lst in
          let end_with_b = (take_while (fun x -> x <> b) start_with_a) @ [b] in
            Eqs end_with_b
        end
      | Path lst ->
        begin
          let start_with_a = drop_while (fun x -> (get_left_expr x) <> a) lst in
          let last = List.find (fun x -> (get_right_expr x) = b) start_with_a in
          let end_with_b = (take_while (fun x -> (get_right_expr x) <> b) start_with_a) @ [last] in
            Path end_with_b
        end

    (* helper for make_proof_local.
     * TODO always keep at least the start and the end of a path *)
    let make_minimal_local_chain prf (belongs_to: expression -> Interval.t) = match prf with
      | Congruence (e1,e2,lst) ->
        begin
          (*this should already be local*)
          assert(common e1 e2 belongs_to);
          [e1;e2]
        end
      | Eqs lst ->
        begin
          (*TODO it is possible to fold from left or right. Currently left.*)
          let rec process acc lst = match lst with
            | x::y::z::xs when common x z belongs_to -> process acc (x::z::xs)
            | x::y::z::xs -> process (x::acc) (y::z::xs)
            | x::y::[] -> List.rev (y::x::acc)
            | _ -> failwith "SatEUF.Proof.make_minimal_local_chain: chain smaller than 2" 
          in
            process [] lst
        end
      | Path lst ->
        begin
          (*TODO it is possible to fold from left or right. Currently left.*)
          let rec process acc e lst = match lst with
            | x::y::xs ->
              begin
                let e2 = get_right_expr y in
                  if common e e2 belongs_to then process acc e (y::xs)
                  else process (e::acc) (get_right_expr x) (y::xs)
              end
            | x::[] -> List.rev ((get_right_expr x)::e::acc)
            | _ -> failwith "SatEUF.Proof.make_minimal_local_chain: chain smaller than 2" 
          in
            process [] (get_left_expr (List.hd lst)) lst
        end
    
    (* helper for make_proof_local.
     * make all the chains have the same length
     * transpose so that each element is all the arguments needed.
     * keeps the beginning and the end of chains + what cross the boundaries
     * TODO is it necessary to keep the extremities ?
     *  Modifying the extremities implies that the rest of the proof has to be also changed
     *  Maybe should be the work of the interpolation method to figure out what to throw away.
     *)
    let equalize_and_transpose lsts belongs_to =
      (*TODO this is the most brutal way => refine *)
      let mins_maxs =
        List.map
          (fun lst ->
            ( List.fold_left (fun acc x -> min acc (Interval.min (belongs_to x))) max_int lst,
              List.fold_left (fun acc x -> max acc (Interval.max (belongs_to x))) (-1) lst) )
          lsts
      in
      let (min, max) =
        List.fold_left
          (fun (mn,mx) (a,b) -> (min mn a, max mx b))
          (List.hd mins_maxs)
          (List.tl mins_maxs)
      in
      let begining = List.map (List.hd) lsts in
      let ending = List.map (fun l -> List.hd (List.rev l)) lsts in
      let find i = List.map (List.find (fun e -> Interval.sub (i, i+1) (belongs_to e) )) lsts in
      let middle = List.map (fun i -> find i) (range min max) in
        uniq (begining :: middle @ [ending])

    (* EUF proofs produced by the solver are not necessarily local (congruence axiom).
     * Therefore we need to rewrite the proof (and introduce new predicates).
     * Example: A -> f(x) = 0 /\ x = y, b -> y = z /\ f(z) = 1.
     * The solver will find that f(x) = f(z), but we want the middle term: f(x) = f(y) = f(z)
     * In that case, a valid interpolant is f(y) = 0 *)
    let rec make_proof_local proof (belongs_to: expression -> Interval.t) = match proof with
      | Congruence (e1,e2,lst) ->
        begin
          let lst' = List.map (fun p -> make_proof_local p belongs_to) lst in
          let chains = List.map (fun p -> make_minimal_local_chain p belongs_to) lst' in
          print_endline (String.concat ", " (List.map print_expr (List.hd chains)));
          let args_chains = equalize_and_transpose chains belongs_to in
          List.iter (fun c -> print_endline (String.concat ", " (List.map print_expr c))) args_chains;
          let args_pairs = pairs_of_list args_chains in
          let args_pairs_and_proof =
            List.map
              (fun (a,b) -> (a, b, List.map2 (fun (a,b) prf -> extract_relevant_part a b prf) (List.combine a b) lst'))
              args_pairs
          in
          let args_pairs_and_proof_str =
            List.map
              (fun (a,b,c) -> (print_expr (List.hd a))^" = "^(print_expr (List.hd b))^" because "^(to_string (List.hd c)))
              args_pairs_and_proof
          in
            print_endline (String.concat "\n" args_pairs_and_proof_str);
            match (e1, e2) with
            | (Application(f1, args1), Application(f2,args2)) ->
              begin
                assert(f1 = f2);
                compact_path (Path (
                  List.map
                    (fun (a1,a2, needed_part) -> Congruence (Application(f1, a1), Application(f2,a2), needed_part))
                    args_pairs_and_proof
                ))
              end
            | _ -> failwith "SatEUF.Proof.make_proof_local: congruence not on Application ??"
        end
      | Eqs lst -> Eqs lst (*should already be local*)
      | Path lst -> Path (List.map (fun p -> make_proof_local p belongs_to) lst)


    (* Keeps only the facts that cross the boundaries. Returns 1 interpolant per boundary.
     * Deals with congruence axioms.
     * Assumes that the proof is local. *)
    let interpolate proof belongs_to =
      (* TODO Normally both extremities of the proof should be common.
       * But the path in the middle can contains local terms that must be eliminated. *)
      (* Also takes care of the congruence axioms
       * Basically, for each argument, project the equality path against the boundary (and adding not the result if it is on the left side).
       * Then, depending on the side of the congruence, combine the pathes with And/Or
       *  if s = A then (A, Or (SatUIF.interpolate_euf true eq (And !a_part_eq) (And !b_part_eq)))
       *  else (B, And (SatUIF.interpolate_euf false eq (And !a_part_eq) (And !b_part_eq))) (*also mixed ?!*)
       *  TODO for mixed, both should be possible ?
       *)
      failwith "TODO"

  end

open Proof


(* proof test *
let non_local =
  Path [
    Eqs [Constant 0.0; Application("f",[Variable "a"])];
    Congruence (Application("f",[Variable "a"]), Application("f", [Variable "c"]), [Eqs([Variable "a"; Variable "b"; Variable "c"])]);
    Eqs [Application("f",[Variable "c"]); Constant 1.0]
  ] 
let belongs_to e = match e with
  | Application("f",[Variable "a"]) -> (1,1)
  | Application("f",[Variable "b"]) -> (1,2)
  | Application("f",[Variable "c"]) -> (2,2)
  | Variable "a" -> (1,1)
  | Variable "b" -> (1,2)
  | Variable "c" -> (2,2)
  | Constant 0.0 -> (1,2)
  | Constant 1.0 -> (1,2)
  | _ -> failwith "ASDF"
let local = make_proof_local non_local belongs_to

let _ =
  print_endline "non_local";
  print_endline (to_string non_local);
  print_endline "local";
  print_endline (to_string local)
**************)

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
      find = Leader (UIGraph.empty, PredSet.empty);
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
      let new_gr = UIGraph.add (UIGraph.merge gr1 gr2) given_this.id given_that.id in
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
                UIGraph.shortest_path graph arg_a arg_b
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

let mk_pred dag (a, b) = 
  let node_a = get dag a in
  let node_b = get dag b in
    Node.mk_eq node_a node_b

let mk_npred dag (a, b) = 
  let node_a = get dag a in
  let node_b = get dag b in
    Not (Node.mk_eq node_a node_b)

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

let current_predicates dag =
  let preds = ref [] in
    Stack.iter
      (fun s -> match s with
        | Equal (pred,_,_) -> preds := pred :: !preds
        | NotEqual (i1, i2) -> preds := (mk_npred dag (i1,i2)) :: !preds
        | _ -> ()
      )
      dag.stack;
    !preds

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

  let mk_pred = mk_pred dag in

  (* is a congruence or not *)
  let raw_congruences = t_deductions dag in
  let all_congruences = List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty raw_congruences in
  let is_congruence pred = PredSet.mem pred all_congruences in
  
  let mk_path n1 n2 graph =
    Message.print Message.Debug (lazy("SatEUF: mk_path for " ^ (print_pred (Node.mk_eq n1 n2)) ^ " in"));
    (*Message.print Message.Debug (lazy(UIGraph.to_string graph));*)
    let path = UIGraph.shortest_path graph n1.Node.id n2.Node.id in
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
              if a1 = a2 then Eqs [a1;a2]
              else
                begin
                  (*check direction of prf*)
                  Message.print Message.Debug (lazy("SatEUF: find_justification args_pairs " ^ (print_expr a1) ^ " and " ^ (print_expr a2)));
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
                    compact_path (Path proofs)
                end
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
  assert(edges <> []);
  let raw_proof = 
    Path (
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
    )
  in
    Message.print Message.Debug (lazy("SatEUF: mk_proof, raw_proof " ^ (Proof.to_string raw_proof)));
    compact_path raw_proof

(*TODO clean up the mess with all these methods that do not quite the same ... *)

(* TODO mk_lemma should return the 'proof' of an equality (congruence or not) using only elements.
 * use the mk_proof method and extract the predicate from there. *)
let mk_lemma dag n1 n2 =
  Message.print Message.Debug (lazy("SatEUF: mk_lemma for " ^ (print_pred (Node.mk_eq n1 n2))));
  let proof = mk_proof dag (Node.mk_eq n1 n2) in
  let raw_congruences = t_deductions dag in
  let needed_congruences = proof_congruences_contained proof in
  let core_set = proof_equalities_contained proof in
  let ordered_info = List.filter (fun x -> PredSet.mem x needed_congruences) raw_congruences in
    Message.print Message.Debug (lazy("SatEUF: needed_congruences = " ^ (String.concat ", " (List.map print_pred (PredSet.elements needed_congruences)))));
    Message.print Message.Debug (lazy("SatEUF: given = " ^ (String.concat ", " (List.map print_pred (PredSet.elements core_set)))));
    (And (PredSet.elements core_set), List.map (fun x -> (x,EUF)) ordered_info)

let lemma_with_info_for dag (c1, c2) =
  let n1 = (get dag c1) in
  let n2 = (get dag c2) in
    assert((Node.find n1).Node.id = (Node.find n2).Node.id);
    mk_lemma dag n1 n2

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
 * TODO this method seems buggy, it does not catch all the propagation ?? *)
let propagations dag shared =
  Message.print Message.Debug (lazy("SatEUF: propagations on " ^ (String.concat "," (List.map print_expr shared))));
  (* 1) get the list of congruence down to the last push *)
  let rec to_last_push () =
    if Stack.is_empty dag.stack
    then []
    (*then failwith "SatEUF: to_last_push found empty stack"*)
    else
      begin
        let top = Stack.pop dag.stack in
        let acc =
          match top with
          | Deduction (_,(id1, f1, c1), (id2, f2, c2),_) -> (f1, f2) :: (to_last_push ())
          | Internal _ -> to_last_push ()
          | Equal _ | NotEqual _ -> []
        in
          Stack.push top dag.stack;
          acc
      end
  in
  (* 2) get the cc down to the last push and project *)
  let int_shared = List.map (fun e -> (get_node dag e).Node.id) shared in
  let graphs_pairs_before =
    List.map
      (fun (f1,f2) -> match (f1,f2) with
        | (Leader (g1,_), Leader (g2, _)) ->
          (UIGraph.project_scc g1 int_shared, UIGraph.project_scc g2 int_shared)
        | _ -> failwith "SatEUF, propagations: expected pairs of leaders"
      )
      (to_last_push ())
  in
  (* 3) make the cc difference to get the new equalities (one equalities per cc merge). *)
  (* need to be carefull with cc, since they contains only the affected equivalence class.
   * therefore, the graph should be fully connected!
   * after projection there should be 0 or 1 scc on each side. *)
  let merge =
    map_filter
      (fun (l1,l2) -> match (l1,l2) with
        | ([scc1],[scc2]) -> Some (IntSet.choose scc1, IntSet.choose scc2)
        | ([],[_]) | ([_],[]) | ([],[]) -> None
        | _ -> failwith ("SatEUF, propagations: merge ("^(string_of_int (List.length l1))^","^(string_of_int (List.length l2))^")" )
      )
      graphs_pairs_before
  in
  let preds = List.map (mk_pred dag) merge in
    preds

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
      let change = Equal (pred, get_node_info t n1'.Node.id, get_node_info t n2'.Node.id) in
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
        | Equal (_,old1, old2) ->
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
