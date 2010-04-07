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

(** Satisfiability for EUF. (UIF stands for UnInterpreted Function symbols)*)

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
(**/**)

(*TODO UIF interpolation*)
(*make those classes extend Dag*)

class node = 
  fun
    (ffname: string) 
    (aargs: node list) -> 
  object (self)
    val fname = ffname
    method get_fname = fname
    
    val args = aargs
    method get_args = args
    
    val arity = List.length aargs
    method get_arity = arity
    
    val mutable ccparent: node list = []
    method set_ccparent lst = ccparent <- lst
    method add_ccparent n = ccparent <- (OrdSet.union ccparent [n])
    method get_ccparent = ccparent
    
    val mutable parent: node option = None
    method set_parent n = parent <- Some n
    method find: node = match parent with
      | None -> (self :> node)
      | Some n ->
        begin 
          let p = n#find in
            parent <- Some p;
            p
        end

    method union (that: node) = 
      let n1 = self#find in
      let n2 = that#find in
        n1#set_parent n2;
        n2#set_ccparent (OrdSet.union n1#get_ccparent n2#get_ccparent);
        n1#set_ccparent []

    method ccpar: node list = (self#find)#get_ccparent

    method congruent (that: node) =
        self#get_fname = that#get_fname
      &&
        self#get_arity = that#get_arity
      &&
        List.for_all (fun (a,b) -> a#find = b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))

    (** return pairs of nodes whose equality may change the result of the 'congruent' method*)
    method may_be_congruent (that: node) =
      if self#get_fname <> that#get_fname
      || self#get_arity <> that#get_arity
      || self#find = that#find then []
      else
        List.filter (fun (a,b) -> a#find <> b#find) (List.rev_map2 (fun x y -> (x,y)) (self#get_args) (that#get_args))

    method merge (that: node) =
      if self#find <> that#find then
        begin
          let p1 = self#ccpar in
          let p2 = that#ccpar in
            self#union that;
            let to_test = Utils.cartesian_product p1 p2 in
              List.iter (fun (x,y) -> if x#find <> y#find && x#congruent y then x#merge y) to_test
        end
    
    (** return pairs of nodes whose equality comes from congruence*)
    method merge_with_applied (that: node) =
      if self#find <> that#find then
        begin
          let p1 = self#ccpar in
          let p2 = that#ccpar in
            self#union that;
            let to_test = Utils.cartesian_product p1 p2 in
              let cong = List.filter (fun (x,y) -> x#find <> y#find && x#congruent y) to_test in
                List.fold_left
                  (fun acc (x,y) -> if x#find <> y#find then
                    (x#merge_with_applied y) @ ((x,y)::acc)
                  else 
                    acc) [] cong
        end
      else []
  end

class dag = fun expr ->
  let table1 = Hashtbl.create 53 in
  let table2 = Hashtbl.create 53 in
  let create_and_add expr fn args =
    try Hashtbl.find table1 expr
    with Not_found ->
      begin
        let n = new node fn args
        in
          Hashtbl.replace table1 expr n;
          Hashtbl.replace table2 n expr;
          n
      end
  in
  let rec convert_exp expr = match expr with
    | Constant c as cst -> create_and_add cst (string_of_float c) []
    | Variable v as var -> create_and_add var v []
    | Application (f, args) as appl ->
      let node_args = (List.map convert_exp args) in
      let new_node  = create_and_add appl f node_args in
        List.iter (fun n -> n#add_ccparent new_node) node_args;
        new_node
    | Sum lst as sum ->
      let node_args = (List.map convert_exp lst) in
      let new_node  = create_and_add sum "+" node_args in
        List.iter (fun n -> n#add_ccparent new_node) node_args;
        new_node
    | Coeff (c, e) as coeff ->
      let node_args = (List.map convert_exp  [Constant c; e]) in
      let new_node  = create_and_add coeff "*" node_args in
        List.iter (fun n -> n#add_ccparent new_node) node_args;
        new_node
  in
  let _ = List.iter (fun x -> ignore (convert_exp x)) expr in
  object (self)
    val nodes: (expression, node) Hashtbl.t = table1
    val node_to_expr: (node, expression) Hashtbl.t = table2
    method get_node expr = Hashtbl.find nodes expr
    method get_expr n = Hashtbl.find node_to_expr n
    method get_nodes = Hashtbl.copy nodes

    val mutable given_eq = PredSet.empty
    method add_eq eq = given_eq <- PredSet.add eq given_eq
    method rm_eq eq = given_eq <- PredSet.remove eq given_eq
    method was_given_eq eq = PredSet.mem eq given_eq
    method get_given_eq = PredSet.fold (fun x acc -> x::acc) given_eq []
    
    val mutable given_neq = PredSet.empty
    method add_neq neq = given_neq <- PredSet.add neq given_neq
    method get_given_neq = PredSet.fold (fun x acc -> x::acc) given_neq []
    method rm_neq neq = given_neq <- PredSet.remove neq given_neq

    method print =
      let buffer = Buffer.create 1000 in
      let print_node (n:node) =
        Buffer.add_string buffer ("node: "^(AstUtil.print_expr (self#get_expr n)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  in class of:  "^(AstUtil.print_expr (self#get_expr n#find)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  ccparent are: "^(Utils.string_list_cat ", " (List.map (fun x -> AstUtil.print_expr (self#get_expr x)) n#get_ccparent)));
        Buffer.add_char buffer '\n';
        Buffer.add_string buffer ("  ccpar    are: "^(Utils.string_list_cat ", " (List.map (fun x -> AstUtil.print_expr (self#get_expr x)) n#ccpar)));
        Buffer.add_char buffer '\n';
      in
        Hashtbl.iter (fun _ n -> print_node n) nodes;
        Buffer.contents buffer

    method add_constr eq = match eq with
      | Eq (e1, e2) ->
        let n1 = self#get_node e1 in
        let n2 = self#get_node e2 in
          self#add_eq eq;
          n1#merge n2
      | _ -> failwith "UIF: 'add_constr' only for Eq"

    (*get the congruence axioms used (OrdSet)*)
    method add_constr_with_applied eq = match eq with
      | Eq (e1, e2) ->
        let n1 = self#get_node e1 in
        let n2 = self#get_node e2 in
          self#add_eq eq;
          List.rev_map (fun (x,y) -> AstUtil.order_eq (Eq (self#get_expr x, self#get_expr y))) (n1#merge_with_applied n2)
      | _ -> failwith "UIF: 'add_constr' only for Eq"

    (*get the congruence axioms used (OrdSet)*)
    method add_pred_with_applied conj =
      let rec split_eq_neq accEq accNeq lst = match lst with
        | (Eq _ as eq)::xs -> split_eq_neq (eq::accEq) accNeq xs
        | (Not (Eq _) as neq)::xs -> split_eq_neq accEq (neq::accNeq) xs
        | [] ->  (accEq,accNeq)
        | err::_ -> failwith ("UIF(1): only for a conjunction of eq/ne "^(AstUtil.print err))
      in
      match conj with
        | And lst ->
          begin
            let (eq,neq) = split_eq_neq [] [] lst in
              List.iter (self#add_neq) neq;
              List.fold_left (fun acc x -> acc @ (self#add_constr_with_applied x) ) [] eq (*TODO change "acc @ ..."*)
          end
        | Eq _ as eq ->
          begin
            self#add_constr_with_applied eq
          end
        | Not (Eq _) as neq ->
          begin
            self#add_neq neq;
            []
          end
        | err -> failwith ("UIF(2): only for a conjunction of eq/ne "^(AstUtil.print err))

   method create_and_add_constr eq = match eq with(*TODO buggy because of congruence parent*)
      | Eq (e1, e2) ->
        let n1 =
            try self#get_node e1
            with Not_found -> convert_exp e1
        in
        let n2 =
            try self#get_node e2
            with Not_found -> convert_exp e2
        in
          self#add_eq eq;
          n1#merge n2
      | _ -> failwith "UIF: 'create_and_add_constr' only for Eq"

    (** is there a contradiction between what DAG and given '!=' *)
    method neq_contradiction neq = match neq with
      | Not (Eq (e1, e2)) ->
        let n1 = self#get_node e1 in
        let n2 = self#get_node e2 in
          self#add_neq neq;
          n1#find = n2#find
      | _ -> failwith "UIF: 'neq_contradiction' only for Not Eq"


    method is_satisfiable conj =
      let rec split_eq_neq accEq accNeq lst = match lst with
        | (Eq _ as eq)::xs -> split_eq_neq (eq::accEq) accNeq xs
        | (Not (Eq _) as neq)::xs -> split_eq_neq accEq (neq::accNeq) xs
        | [] ->  (accEq,accNeq)
        | c -> failwith ("UIF: only for a conjunction of eq/ne, given: "^(Utils.string_list_cat ", " (List.map AstUtil.print c)))
      in
      match conj with
        | And lst ->
          begin
            let (eq,neq) = split_eq_neq [] [] lst in
              Message.print Message.Debug (lazy("EUF GRAPH before:\n"^self#print));
              List.iter (self#add_constr) eq;
              Message.print Message.Debug (lazy("EUF GRAPH after:\n"^self#print));
              not (List.exists self#neq_contradiction neq)
          end
        | err -> failwith ("UIF: only for a conjunction of eq/ne"^(AstUtil.print err))

    (** Tests if the '!=' are respected and return the failing cstrs*)
    method test_for_contradition =
      let failing = PredSet.filter self#neq_contradiction given_neq in
        PredSet.fold (fun x acc -> x::acc) failing []

    (** for incremental use *)
    method has_contradiction =
      PredSet.exists self#neq_contradiction given_neq

    (** Gets a list of list of equal expressions (connected components). *)
    method get_cc =
      let node_to_cc = Hashtbl.create (Hashtbl.length nodes) in
        Hashtbl.iter (fun e n ->
            let parent = n#find in
            let already =
              try Hashtbl.find node_to_cc parent
              with Not_found -> []
            in
              Hashtbl.replace node_to_cc parent (e::already)
          ) nodes;
        Hashtbl.fold (fun _ cc acc -> cc::acc) node_to_cc []

    (** is given eq true in all cases ?
     *)
    method entailed eq =
      match eq with
      | Eq(e1,e2) ->
        begin
          let n1 = (self#get_node e1)#find in
          let n2 = (self#get_node e2)#find in
            n1 = n2
        end
      | _ -> failwith "SatUIF, entailed: expected EQ"

    (** Returns a list of new deduced equalities.
     *  The returned equalities are then put in the set of equalities.
     *)
    method new_equalities =
      let new_eq = ref [] in
      let cc = self#get_cc in
        List.iter
          (fun x ->
            ignore (List.fold_left
              (fun acc y ->
                List.iter
                  (fun x ->
                    let eq = AstUtil.order_eq (Eq(x,y)) in
                      if not (self#was_given_eq eq)  then
                        begin
                          self#add_eq eq;
                          new_eq := eq::(!new_eq)
                        end
                  ) acc;
                y::acc
              ) [] x
            )
          ) cc;
        !new_eq


    (** Returns a list equalities that may change the graph.
     *  This method is for nelson oppen: it is the equalities
     *  that the LI solver needs to check.
     *)
    method relevant_equalites =
      let eqs = ref PredSet.empty in
      let cc = self#get_cc in
        let rec process lst = match lst with
          | _::[] | [] -> ()
          | x::xs ->
            let fxs = List.flatten xs in
              List.iter (
                fun e1 ->
                  List.iter (
                    fun e2 ->
                      let n1 = self#get_node e1 in
                      let n2 = self#get_node e2 in
                      let pairs = n1#may_be_congruent n2 in
                      (*TODO cc_pairs may be a bottle neck...*)
                      let cc_pairs = List.map (fun (x,y) -> (
                            List.hd (List.filter (List.mem (self#get_expr x)) cc),
                            List.hd (List.filter (List.mem (self#get_expr y)) cc)
                          )) pairs
                      in
                      let uniq_cc_pairs = OrdSet.list_to_ordSet cc_pairs in
                        List.iter (
                          fun (x,y) ->
                            List.iter (fun e1 ->
                              List.iter (fun e2 ->
                                  eqs := PredSet.add (AstUtil.order_eq (Eq (e1, e2))) !eqs
                                ) y
                              ) x
                          ) uniq_cc_pairs
                    ) fxs
                ) x;
              process xs
        in
          process cc;
          PredSet.fold (fun x acc -> x::acc) !eqs []

    (** tells if the given equalities may change the graph *)
    method is_relevant_equality eq = match eq with
      | Eq (e1,e2) ->
        begin
          let n1 = self#get_node e1 in
          let n2 = self#get_node e2 in
            n1 <> n2
        end
      | err -> failwith ("satUIF, is_relevant_equality: found "^(AstUtil.print err))


    (** Returns the 'projection' of the graph on a set of restricted variables.
     *  Assumes that the graph is in a satisfiable state
     *  @param vars a list of expression considered as the target terms
     *)
    method project vars =
      let template: (node * node) list ref = ref [] in
        (*makes the templates*)
        PredSet.iter (
          fun x -> match x with 
            | Not (Eq (e1, e2)) ->
              begin
                let n1 = (self#get_node e1)#find in
                let n2 = (self#get_node e2)#find in
                let pair = if n1 < n2 then (n1,n2)
                           else if n2 < n1 then (n2,n1)
                           else failwith "satUIF: project, system is unsat."
                in
                  template := OrdSet.union !template [pair]
              end
            | e -> failwith ("satUIF: given_neq contains something strange: "^(AstUtil.print e))
          ) given_neq;
        (*fill one side of the template*)
        let half_instanciated: (expression * node) list ref  = ref [] in
          List.iter (
            fun v ->
              try
                let n = (self#get_node v)#find in
                  List.iter (
                    fun (t1,t2) ->
                      if n = t1 then
                        half_instanciated:= OrdSet.union !half_instanciated [(v,t2)];
                      if n = t2 then
                        half_instanciated:= OrdSet.union !half_instanciated [(v,t1)]
                    ) !template
              with Not_found ->
                () (*new var ??*)
            ) vars;
          (*fill the other side of the template*)
          let instanciated = ref PredSet.empty in
            List.iter (
              fun v ->
                try
                  let n = (self#get_node v)#find in
                    List.iter (
                      fun (e1,t2) ->
                        if n = t2 then
                          instanciated:= PredSet.add (Not (AstUtil.order_eq (Eq (e1,v)))) !instanciated
                      ) !half_instanciated
                with Not_found ->
                  () (*new var ??*)
              ) vars;
            instanciated := PredSet.remove True !instanciated; (*just in case*)
            (*now the eq*)
            let rec process_eq todo = match todo with
              | x::xs ->
                begin 
                  try
                    let n1 = (self#get_node x)#find in
                      List.iter (
                        fun y ->
                          try
                            let n2 = (self#get_node y)#find in
                              if n1 = n2 then
                                instanciated := PredSet.add (AstUtil.order_eq (Eq(x,y))) !instanciated
                          with Not_found -> ()
                      ) xs
                  with Not_found -> ()
                end;
                process_eq xs
              | [] -> ()
            in
              process_eq vars;
              PredSet.fold (fun x acc -> x::acc) !instanciated []

    method copy =
      let expressions = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = new dag expressions in
      let new_of_old = Hashtbl.create (List.length expressions) in
        List.iter (fun e -> Hashtbl.add new_of_old (self#get_node e) (cp#get_node e) ) expressions;
        List.iter (fun e ->
          let new_node = cp#get_node e in
          let old_node = self#get_node e in 
            new_node#set_ccparent (List.map (Hashtbl.find new_of_old) (old_node#get_ccparent));
            let new_parent = Hashtbl.find new_of_old (old_node#find) in
              if new_parent <> new_node then new_node#set_parent new_parent
          ) expressions;
        List.iter (cp#add_eq) (self#get_given_eq);(*TODO avoid unnecessary list*)
        List.iter (cp#add_neq) (self#get_given_neq);(*TODO avoid unnecessary list*)
        cp

    method copy_and_extand expr =
      let expressions = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = new dag (expressions @ expr) in
      let new_of_old = Hashtbl.create (List.length expressions) in
        List.iter (fun e -> Hashtbl.add new_of_old (self#get_node e) (cp#get_node e) ) expressions;
        List.iter (fun e ->
          let new_node = cp#get_node e in
          let old_node = self#get_node e in 
            new_node#set_ccparent (List.map (Hashtbl.find new_of_old) (old_node#get_ccparent));
            let new_parent = Hashtbl.find new_of_old (old_node#find) in
              if new_parent <> new_node then new_node#set_parent new_parent
          ) expressions;
        List.iter (cp#add_eq) (self#get_given_eq);(*TODO avoid unnecessary list*)
        List.iter (cp#add_neq) (self#get_given_neq);(*TODO avoid unnecessary list*)
        cp

    method merge (graph: dag) =
      let expr = Hashtbl.fold (fun e _ acc -> e::acc ) nodes [] in
      let cp = graph#copy_and_extand expr in
        PredSet.iter cp#add_constr given_eq;
        PredSet.iter cp#add_neq given_neq;
        cp (*TODO avoid add_constr (does the job again...)*)

  end

let is_uif_sat pred =
  let expr = AstUtil.get_expr pred in
  let graph = new dag expr in
    graph#is_satisfiable pred


let common_expression a b =
  let common_var =  OrdSet.intersection (AstUtil.get_var a) (AstUtil.get_var b) in
  let common_sym =  OrdSet.intersection (AstUtil.get_fct_sym a) (AstUtil.get_fct_sym b) in
    Message.print Message.Debug (lazy("common variables are: " ^ (Utils.string_list_cat ", " (List.map AstUtil.print_expr common_var))));
    Message.print Message.Debug (lazy("common fct are: " ^ (Utils.string_list_cat ", " common_sym)));
    (common_sym, common_var)

(*TODO refactore*)
(** is only an over-approximation*)
let unsat_core formula =
  Message.print Message.Debug (lazy ("SatUIF, unsat core for "^(AstUtil.print formula)));
  let expr = AstUtil.get_expr formula in
  let graph = new dag expr in
  let f_parts = AstUtil.get_subterm_nnf formula in
  let ded_with_order = List.filter (fun x -> not (List.mem x f_parts)) (graph#add_pred_with_applied formula) in (*avoid justifing given eq*)
  let previous_ded eq =
    let rec process acc lst = match lst with
      | x :: xs ->
        if x = eq then List.rev acc else process (x::acc) xs
      | [] -> failwith "SatUIF, previous_ded: deduction not found"
    in
      process [] ded_with_order
  in
  let ded = ref (OrdSet.list_to_ordSet ded_with_order) in
  let justified = ref [] in
    if not (graph#has_contradiction) then 
      raise (SAT_FORMULA formula)
    else
      begin
        let formula_lst = match formula with
          | And lst -> lst
          | _ -> failwith "SatUIF: unsat_core (1)"
        in
        let eqs = ref (fst (EqDag.split_eq_neq [] [] formula_lst)) in
          match List.hd (graph#test_for_contradition) with
          | Not (Eq(e1,e2)) as neq ->
            begin
              let path = EqDag.bfs (!ded @ !eqs) e1 e2 in
              let proof = EqDag.path_to_eq path in
              let rec justify_ded eq =
                if OrdSet.mem eq !ded then
                  begin (*need a deduced eq*)
                    Message.print Message.Debug (lazy((AstUtil.print eq )^" is deduced"));
                    let prev = OrdSet.list_to_ordSet (previous_ded eq) in
                      match eq with
                      | Eq(Application(_,args1),Application(_,args2))
                      | Eq(Sum args1, Sum args2) -> (*Sum as UF*)
                        begin
                          let justification = List.map2 (fun x y ->
                              if x = y then True
                              else
                                begin
                                  let path = EqDag.bfs (prev @ !eqs) x y in (*TODO Not_Found*)
                                  let proof = EqDag.path_to_eq path in
                                    And (List.map justify_ded proof)
                                end
                            ) args1 args2
                          in
                            ded := OrdSet.subtract !ded [eq];(*justify only once*)
                            eqs := eq::(!eqs);
                            justified := eq::(!justified);
                            And justification
                        end
                      | Eq(Coeff(c1,e1), Coeff(c2,e2)) -> (*coeff as UF*)
                        begin
                          let justification = List.map2 (fun x y ->
                              if x = y then True
                              else
                                begin
                                  let path = EqDag.bfs (prev @ !eqs) x y in
                                  let proof = EqDag.path_to_eq path in
                                    And (List.map justify_ded proof)
                                end
                            ) [Constant c1; e1] [Constant c2; e2]
                          in
                            ded := OrdSet.subtract !ded [eq];(*justify only once*)
                            eqs := eq::(!eqs);
                            justified := eq::(!justified);
                            And justification
                        end
                      | err -> failwith ("SatUIF: unsat_core (3), "^(AstUtil.print err))
                    end
                else
                  begin
                    Message.print Message.Debug (lazy((AstUtil.print eq )^" is given"));
                    if List.mem eq !justified then True else eq (*present in the original system*)
                  end
              in
              let core = AstUtil.normalize_only (And (neq::(List.map justify_ded proof))) in
                core
            end
          | _ -> failwith "SatUIF: unsat_core (2)"
      end

let find_common_expr a b ea eb common_var common_sym =
  match (a,b,ea,eb) with
  | (And a_lst, And b_lst, Application(fa, argsa) ,Application(fb,argsb)) ->
    begin
      let args = List.map2
        (fun arg brg ->
          if arg <> brg then EqDag.find_common_expr arg brg (a_lst @ b_lst) common_var common_sym
          else arg
        )
        argsa argsb
      in
        assert(Global.is_off_assert() || fa=fb);
        Application(fa, args) 
    end
  | _ -> failwith "SatUIF, find_common_expr: expected Ands and Applications"


(** This method is more restrictive than its name says.
 * It is supposed to interpolate in a specific case of the NelsonOppen framework.
 * 
 * it assumes:
 *  a /\ b contains no negation.
 * @param  a_side eq is applied to in A/B part.
 * @param  eq is an application of the congruence axiom, such that (Not eq) is a contradiction.
 * @param  a the A formula.
 * @param  b the B formula.
 *)
let interpolate_euf a_side eq a b =
  let a_expr = AstUtil.get_expr a in
  let b_expr = AstUtil.get_expr b in

  let graph_a = new EqDag.dag a_expr in
  let graph_b = new EqDag.dag b_expr in
    ignore (graph_a#is_satisfiable a, graph_b#is_satisfiable b);
    match eq with
    | Eq (Application(_, args1), Application(_, args2)) ->
      begin
        let args = List.map2
          (fun a b ->
            let eq = AstUtil.order_eq (Eq(a,b)) in
              if a_side then
                begin
                  graph_a#create_needed_nodes eq;
                  graph_a#add_neq (Not eq)
                end
              else
                begin
                  graph_b#create_needed_nodes eq;
                  graph_b#add_neq (Not eq)
                end;
              let it =
                try
                  EqDag.interpolate_from_graph graph_a graph_b
                with SAT ->
                  False
              in
                if a_side then graph_a#remove_neq (Not eq) else graph_b#remove_neq (Not eq);
                it
          )
          args1 args2
        in
          args
      end
    | _ -> failwith "SatUIF, interpolate_euf: expected Ands"


(*********************************)
(** The different changes that can happen in the system *)
type find_t =  int * (predicate list)
type euf_change = StackEq of predicate * (int * find_t * IntSet.t) * (int * find_t * IntSet.t) (* eq + 2 x (id,find,ccpar) *)
                | StackNeq of predicate 
                | StackTDeduction of predicate * (int * find_t * IntSet.t) * (int * find_t * IntSet.t) (*application of the congruence axiom*)
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

module Dag: sig
    type t = {
      nodes: Node.t array;
      expr_to_node: (expression, Node.t) Hashtbl.t;
      stack: euf_change Stack.t;
      mutable neqs: (int * int) list (* neqs as pairs of node id *)
    }

    val create: PredSet.t -> t
    val get: t -> int -> Node.t
    val get_node: t -> expression -> Node.t
    val is_sat: t -> bool
    val push: t -> predicate -> bool
    val pop: t -> unit
    val propagation: t -> expression list -> predicate list
    val congruences: t -> predicate list
    val unsat_core_with_info: t -> (predicate * theory * (predicate * theory) list)
    val unsat_core: t -> predicate
  end
  =
  struct
    type t = {
      nodes: Node.t array;
      expr_to_node: (expression, Node.t) Hashtbl.t;
      stack: euf_change Stack.t;
      mutable neqs: (int * int) list (* neqs as pairs of node id *)
    }

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
      )
    
    let push dag pred =
      if not (is_sat dag) then
        failwith "EUF: pusch called on an already unsat system.";
      match pred with
      | Eq (e1, e2) ->
        begin
          let n1 = get_node dag e1 in
          let n2 = get_node dag e2 in
            Node.merge n1 n2;
            is_sat dag
        end
      | Not (Eq(e1, e2)) ->
        begin
          let n1 = get_node dag e1 in
          let n2 = get_node dag e2 in
            dag.neqs <- (n1.Node.id, n2.Node.id) :: dag.neqs;
            Stack.push (StackNeq pred) dag.stack;
            is_sat dag
        end
      | err -> failwith ("EUF: push only for an eq/ne "^(AstUtil.print err))

    let pop dag =
      let undo (id, find, parent) =
        let n = get dag id in
          n.Node.find <- find;
          n.Node.ccpar <- parent
      in
      let rec process () =
        if Stack.is_empty dag.stack then
          failwith "EUF: pop called on an empty stack"
        else
          begin
            let t = Stack.pop dag.stack in
              match t with
              | StackEq ((Eq (e1,e2)), old1, old2) ->
                begin
                  undo old1;
                  undo old2;
                  assert(Global.is_off_assert() || 
                    is_sat dag
                  )
                end
              | StackNeq (Not (Eq (e1,e2))) ->
                begin
                  assert(Global.is_off_assert() || 
                    (List.hd dag.neqs) = ((get_node dag e1).Node.id, (get_node dag e2).Node.id)
                  );
                  dag.neqs <- List.tl dag.neqs;
                  assert(Global.is_off_assert() || 
                    is_sat dag
                  )
                end
              | StackInternal (id, find) ->
                begin
                  (get dag id).Node.find <- find;
                  process ()
                end
              | StackTDeduction (eq, old1, old2) ->
                begin
                  undo old1;
                  undo old2;
                  process ()
                end
              | _ -> failwith ("EUF: pop called with unexpected arugments")
          end
      in
        process ()

    (* Propagation on given variables ...
     * the given expressions are assumed to be not kown equal *)
    let propagation dag variables =
      (*
      let rec inspect_stack () =
        if Stack.is_empty dag.stack then []
        else
          begin
            let t = Stack.pop dag.stack in
            let ans = match t with
              | StackEq _ | StackNeq _ -> []
              | StackInternal _ -> inspect_stack ()
              | StackTDeduction (t_eq, _, _) -> t_eq :: (inspect_stack ())
            in
              Stack.push t dag.stack;
              ans
          end
      in
      let new_deductions = inspect_stack () in
      *)
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
    
    let congruences dag =
      let rec inspect_stack () =
        if Stack.is_empty dag.stack then []
        else
          begin
            let t = Stack.pop dag.stack in
            let ans = match t with
              | StackEq _ | StackNeq _ | StackInternal _ -> inspect_stack ()
              | StackTDeduction (t_eq, _, _) -> t_eq :: (inspect_stack ())
            in
              Stack.push t dag.stack;
              ans
          end
      in
        inspect_stack ()

    let unsat_core_with_info dag =
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

    let unsat_core dag = 
      let (core, _, _) = unsat_core_with_info dag in
        core
  end

