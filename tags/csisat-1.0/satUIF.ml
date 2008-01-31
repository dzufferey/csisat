(*  CSIsat: interpolation procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

open Ast

(*TODO UIF interpolation*)
(*make those classes extand Dag*)

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
        that#set_ccparent (OrdSet.union n1#get_ccparent that#get_ccparent);
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
            let to_test = OrdSet.cartesian_product p1 p2 in
              List.iter (fun (x,y) -> if x#find <> y#find && x#congruent y then x#merge y) to_test
        end
    
    (** return pairs of nodes whose equality comes from congruence*)
    method merge_with_applied (that: node) =
      if self#find <> that#find then
        begin
          let p1 = self#ccpar in
          let p2 = that#ccpar in
            self#union that;
            let to_test = OrdSet.cartesian_product p1 p2 in
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

    val mutable given_eq = AstUtil.PredSet.empty
    method add_eq eq = given_eq <- AstUtil.PredSet.add eq given_eq
    method was_given_eq eq = AstUtil.PredSet.mem eq given_eq
    method get_given_eq = AstUtil.PredSet.fold (fun x acc -> x::acc) given_eq []
    
    val mutable given_neq = AstUtil.PredSet.empty
    method add_neq neq = given_neq <- AstUtil.PredSet.add neq given_neq
    method get_given_neq = AstUtil.PredSet.fold (fun x acc -> x::acc) given_neq []

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
        | err::_ -> failwith ("UIF: only for a conjunction of eq/ne"^(AstUtil.print err))
      in
      match conj with
        | And lst ->
          begin
            let (eq,neq) = split_eq_neq [] [] lst in
              List.iter (self#add_neq) neq;
              List.fold_left (fun acc x -> acc @ (self#add_constr_with_applied x) ) [] eq (*TODO change "acc @ ..."*)
          end
        | err -> failwith ("UIF: only for a conjunction of eq/ne"^(AstUtil.print err))

   method create_and_add_constr eq = match eq with(*TODO buggy*)
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
        | c -> failwith ("UIF: only for a conjunction of eq/ne, given:"^(Utils.string_list_cat ", " (List.map AstUtil.print c)))
      in
      match conj with
        | And lst ->
          begin
            let (eq,neq) = split_eq_neq [] [] lst in
              List.iter (self#add_constr) eq;
              not (List.exists self#neq_contradiction neq)
          end
        | err -> failwith ("UIF: only for a conjunction of eq/ne"^(AstUtil.print err))

    (* test if the '!=' are respected and return the failing cstrs*)
    method test_for_contradition =
      let failing = AstUtil.PredSet.filter self#neq_contradiction given_neq in
        AstUtil.PredSet.fold (fun x acc -> x::acc) failing []

    (* for incremental use *)
    method has_contradiction =
      AstUtil.PredSet.exists self#neq_contradiction given_neq

    (** get a list of list of equal expressions *)
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

    (** return a list of new deduced equalities
     *  the returned equalities are then put in the set of equalities
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


    (** return a list a equalities that may change the graph
     *  this method is for nelson oppen, it is the equalities
     *  that the LI solver needs to check
     *)
    method relevant_equalites =
      let eqs = ref AstUtil.PredSet.empty in
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
                                  eqs := AstUtil.PredSet.add (AstUtil.order_eq (Eq (e1, e2))) !eqs
                                ) y
                              ) x
                          ) uniq_cc_pairs
                    ) fxs
                ) x;
              process xs
        in
          process cc;
          AstUtil.PredSet.fold (fun x acc -> x::acc) !eqs []

    (** tells if the given equalities may change the graph *)
    method is_relevant_equality eq = match eq with
      | Eq (e1,e2) ->
        begin
          let n1 = self#get_node e1 in
          let n2 = self#get_node e2 in
            n1 <> n2
        end
      | err -> failwith ("satUIF, is_relevant_equality: found "^(AstUtil.print err))


    (** return the 'projection' of the graph on a set of
     *  restricted variable
     *  assume that the graph is in a satisfiable state
     *  @param vars a list of expression considered as UIF term
     *)
    method project vars =
      let template: (node * node) list ref = ref [] in
        (*makes the templates*)
        AstUtil.PredSet.iter (
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
          let instanciated = ref AstUtil.PredSet.empty in
            List.iter (
              fun v ->
                try
                  let n = (self#get_node v)#find in
                    List.iter (
                      fun (e1,t2) ->
                        if n = t2 then
                          instanciated:= AstUtil.PredSet.add (Not (AstUtil.order_eq (Eq (e1,v)))) !instanciated
                      ) !half_instanciated
                with Not_found ->
                  () (*new var ??*)
              ) vars;
            instanciated := AstUtil.PredSet.remove True !instanciated; (*just in case*)
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
                                instanciated := AstUtil.PredSet.add (AstUtil.order_eq (Eq(x,y))) !instanciated
                          with Not_found -> ()
                      ) xs
                  with Not_found -> ()
                end;
                process_eq xs
              | [] -> ()
            in
              process_eq vars;
              AstUtil.PredSet.fold (fun x acc -> x::acc) !instanciated []

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
        AstUtil.PredSet.iter cp#add_constr given_eq;
        AstUtil.PredSet.iter cp#add_neq given_neq;
        cp (*TODO avoid add_constr (does the job again...)*)

    (*TODO merge with relvent equalities ... *)

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

(*TODO this is complete, but is it sound ??(i.e. on  shared expr)*)
let interpolate_uif a b =
  let expr_a = AstUtil.get_expr_deep a in
  let expr_b = AstUtil.get_expr_deep b in
  (*let common = OrdSet.intersection (OrdSet.list_to_ordSet expr_a) (OrdSet.list_to_ordSet expr_b) in*)
  let (common_sym, common_var) = common_expression a b in
  let graph_a = new dag (expr_a) in
  let sat_a = graph_a#is_satisfiable a in
    if not sat_a then False
    else
      begin
        (*A is sat*)
        let graph_b = new dag expr_b in
        let sat_b = graph_b#is_satisfiable b in
        if not sat_b then True
        else
          begin
            (*A and B are sat*)
            let rec split accEq accNeq lst = match lst with
              | (Eq _ as eq)::xs -> split (eq::accEq) accNeq xs
              | (Not(Eq _) as neq)::xs -> split accEq (neq::accNeq) xs
              | e::xs -> failwith ("satUIF, interpolate_uif(1): projection contains some strang term -> "^(AstUtil.print e))
              | [] -> (accEq,accNeq)
            in
            let (eq_a,neq_a) = match a with
              | And lst_a -> split [] [] lst_a
              | _ -> failwith "satUIF, interpolate_uif(2a): ...."
            in
            let (eq_b,neq_b) = match b with
              | And lst_b -> split [] [] lst_b
              | _ -> failwith "satUIF, interpolate_uif(2b): ...."
            in
            let graph_all = new dag (expr_a @ expr_b) in
              List.iter (fun x -> graph_all#add_constr x) eq_a;
              List.iter (fun x -> graph_all#add_constr x) eq_b;
              let expr_only vars sym expr =
                let rec process expr = match expr with
                  | Constant _ as c -> List.mem c vars
                  | Variable _ as v -> List.mem v vars
                  | Application (s, lst) -> (List.mem s sym) && (List.for_all process lst)
                  | _ -> false (*should not happen*)
                in
                  process expr
              in
              let rec max_depth expr =
                let max_val = ref 0 in
                match expr with
                  | Application (s, lst) ->
                    begin
                      List.iter (fun x -> max_val := max (max_depth x) !max_val ) lst;
                      1 + !max_val
                    end
                  | _ -> 0
              in
              let allowed_sym sym expr = match expr with
                | Application (s, _) -> (List.mem s sym)
                | _ -> false
              in
              let build_interpolant graph e1 e2 =
                let cc = graph#get_cc in
                let stack = ref [] in
                let rec get_equiv expr =
                  let cur_cc = List.hd (List.filter (List.mem expr) cc) in
                  let lucky = List.filter (expr_only common_var common_sym) cur_cc in
                  if List.length lucky > 0 then
                    begin
                      Some(List.hd lucky)
                    end
                  else
                    (*DFS*)
                    begin
                      if List.mem expr !stack then
                        None (*cycle detection*)
                      else
                        let possible_term = List.filter (allowed_sym common_sym) cur_cc in
                          stack := expr::(!stack);
                          let fill_sub expr = match expr with
                            | Application (s, lst) ->
                            (*TODO if s is not a common symbol*)
                              let args = List.map get_equiv lst in
                                if List.for_all (fun x -> x <> None ) args then
                                    Some (Application(s, Utils.remove_some args))
                                else None
                            | _ -> failwith "satUIF: ..."
                          in
                          let rec find_possible lst = match lst with
                            | x::xs ->
                              begin
                                match fill_sub x with
                                | None -> find_possible xs
                                | x -> x
                              end
                            | [] -> None
                          in
                          let res = find_possible possible_term in
                            stack := List.tl (!stack);
                            res
                    end
                in
                  let ee1 = get_equiv e1 in
                  let ee2 = get_equiv e2 in
                    match (ee1, ee2) with
                    | (Some x, Some y) -> Eq(x,y)
                    | _ -> False
              in
                let contra_a = List.filter graph_all#neq_contradiction neq_a in
                let it_a = List.filter (fun x -> x <> Not False) (List.map (fun x -> match x with
                  | Not(Eq (e1,e2)) -> Not (build_interpolant graph_a e1 e2)
                  | _ -> failwith "satUIF, interpolate_uif(3): ...."
                  ) contra_a)
                in
                  match ((List.length contra_a) > 0, (List.length it_a) > 0) with
                  | (true, true) -> List.hd it_a
                  | (true, false) -> failwith "satUIF, interpolate_uif(4): contradiction found, but unable to build interpolant"
                  | (false, _) ->
                    begin
                      let contra_b = List.filter graph_all#neq_contradiction neq_b in
                      let it_b = List.filter (fun x -> x <> False) (List.map (fun x -> match x with
                        | Not(Eq (e1,e2)) -> build_interpolant graph_b e1 e2
                        | _ -> failwith "satUIF, interpolate_uif(5): ...."
                        ) contra_b)
                      in
                        match ((List.length contra_b) > 0, (List.length it_b) > 0) with
                        | (true, true) -> List.hd it_b
                        | (true, false) -> failwith "satUIF, interpolate_uif(6): contradiction found, but unable to build interpolant"
                        | (false, _) -> raise SAT
                    end
          end
      end
  
let interpolate a b =
  interpolate_uif a b

(*May be only an over-approximation*)
let unsat_core formula =
  Message.print Message.Debug (lazy ("SatUIF, unsat core for "^(AstUtil.print formula)));
  let expr = AstUtil.get_expr formula in
  let graph = new dag expr in
  let f_parts = AstUtil.get_subterm_nnf formula in
  let ded = graph#add_pred_with_applied formula in
  let ded = List.filter (fun x -> not (List.mem x f_parts)) ded in (*avoid justifing given eq*)
    if not (graph#has_contradiction) then 
      raise (SAT_FORMULA formula)
    else
      begin
        let formula_lst = match formula with
          | And lst -> lst
          | _ -> failwith "SatUIF: unsat_core (1)"
        in
        let eqs = fst (Dag.split_eq_neq [] [] formula_lst) in
          match List.hd (graph#test_for_contradition) with
          | Not (Eq(e1,e2)) as neq ->
            begin
              let path = Dag.bfs (ded @ eqs) e1 e2 in
              let proof = Dag.path_to_eq path in
              let rec justify_ded eq =(*TODO can this goes into an infinite loop (circular proof) ??*)
                if List.mem eq ded then
                  begin (*need a deduced eq*)
                    Message.print Message.Debug (lazy((AstUtil.print eq )^" is deduced"));
                    match eq with
                    | Eq(Application(_,args1),Application(_,args2))
                    | Eq(Sum args1, Sum args2) -> (*Sum as UF*)
                      begin
                        let justification = List.map2 (fun x y ->
                            if x = y then True
                            else
                              begin
                                let path = Dag.bfs (ded @ eqs) x y in
                                let proof = Dag.path_to_eq path in
                                  And (List.map justify_ded proof)
                              end
                          ) args1 args2
                        in
                          And justification
                      end
                    | Eq(Coeff(c1,e1), Coeff(c2,e2)) -> (*coeff as UF*)
                      begin
                        let justification = List.map2 (fun x y ->
                            if x = y then True
                            else
                              begin
                                let path = Dag.bfs (ded @ eqs) x y in
                                let proof = Dag.path_to_eq path in
                                  And (List.map justify_ded proof)
                              end
                          ) [Constant c1; e1] [Constant c2; e2]
                        in
                          And justification
                      end
                    | err -> failwith ("SatUIF: unsat_core (3), "^(AstUtil.print err))
                  end
                else
                  begin
                    Message.print Message.Debug (lazy((AstUtil.print eq )^" is given"));
                    eq (*present in the original system*)
                  end
              in
              let core = AstUtil.normalize_only (And (neq::(List.map justify_ded proof))) in
                core
            end
          | _ -> failwith "SatUIF: unsat_core (2)"
      end
