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

let rec print_expr expr = match expr with
  | Constant cst -> string_of_float cst
  | Variable v -> v
  | Application (sym, lst) -> sym ^ "(" ^ (Utils.string_list_cat ", " (List.map print_expr lst)) ^")"
  | Sum lst ->  "(" ^ (Utils.string_list_cat " + " (List.map print_expr lst)) ^")"
  | Coeff (co, expr) -> (string_of_float co) ^ "*" ^ (print_expr expr)

let rec print_pred p =
  match p with
  | False -> "false"
  | True -> "true"
  | And lst -> "And [ " ^ (Utils.string_list_cat ", " (List.map print_pred lst)) ^"]"
  | Or lst -> "Or [ " ^ (Utils.string_list_cat ", " (List.map print_pred lst)) ^"]"
  | Not p -> "not " ^ print_pred p
  | Eq (e1,e2) -> "("^(print_expr e1) ^ " = " ^ (print_expr e2)^")"
  | Lt (e1,e2) -> "("^(print_expr e1) ^ " < " ^ (print_expr e2)^")"
  | Leq (e1,e2) -> "("^(print_expr e1) ^ " <= " ^ (print_expr e2)^")"
  | Atom i -> "atom"^(string_of_int i)

let print p = print_pred p
 
let rec push_negation negate pred = match pred with
  | True when negate -> False
  | True -> True
  | False when negate -> True
  | False -> False
  | Not pred -> push_negation (not negate) pred
  | And lst when negate -> Or (List.map (push_negation negate) lst) 
  | And lst -> And (List.map (push_negation negate) lst) 
  | Or lst when negate -> And (List.map (push_negation negate) lst) 
  | Or lst -> Or (List.map (push_negation negate) lst) 
  | Lt (e1,e2) when negate -> Leq (e2, e1)
  | Leq (e1,e2) when negate -> Lt (e2, e1)
  | p when negate -> Not p
  | p -> p

(*TODO
    distribute_coeff
    flatten Sum
    merge coeff + sort
    delete uneeded term
    remove uneeded coeff
*)
(* BUG -1 * f[x]
*)
let rec simplify_expr expr = 
  let rec distribute_coeff coeff expr =
    match expr with
    | Constant c1 -> Constant (coeff *. c1)
    | Variable _ as v -> Coeff (coeff, v)
    | Application (sym, lst) -> Coeff(coeff, Application(sym, List.map (distribute_coeff 1.0) lst))
    | Sum lst -> Sum (List.map (distribute_coeff coeff) lst)
    | Coeff (c,e) -> distribute_coeff (coeff *. c) e
  in
  let rec flatten expr = 
    match expr with
    | Constant _ as c -> c
    | Variable _ as e -> e
    | Application (sym, lst) -> Application(sym, List.map flatten lst)
    | Sum lst -> Sum (List.fold_left ( fun acc x -> match x with
        | Sum lst -> lst @ acc
        | _ as exp -> exp::acc ) [] (List.map flatten lst))
    | Coeff (c,e) -> Coeff(c, flatten e)
  in
  let rec merge_cst expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map merge_cst lst)
    | Sum lst ->
      let res = List.fold_left (fun (cst,lst) x -> match x with
        | Constant c -> (cst +. c, lst)
        | Variable _ as v -> (cst, v::lst)
        | Application (sym, flst) -> (cst, Application(sym, List.map merge_cst flst)::lst)
        | Sum lst -> failwith "Sum should be flattenend"
        | Coeff (c, Application(sym, flst)) -> (cst, Coeff(c, Application(sym, List.map merge_cst flst))::lst)
        | Coeff (c, Variable _) as co -> (cst, co::lst)
        | Coeff (_, Constant _) | Coeff(_, Sum _) | Coeff(_, Coeff _)-> failwith "merge_cst: arg not normalized"
        ) (0.0, []) lst
      in Sum((Constant (fst res))::(snd res))
    | Coeff (c, Application(sym, flst)) -> Coeff(c, Application(sym, List.map merge_cst flst))
    | Coeff _ as co -> co
  in
  let rec get_var expr =
    match expr with
    | Constant _ -> []
    | Variable _ as v -> [v]
    | Application (sym, lst) -> List.fold_left (fun acc x -> OrdSet.union (get_var x) acc) [] lst
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (get_var x) acc) [] lst
    | Coeff (c,e) -> get_var e
  in
  let rec merge_var var expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, flst) -> Application(sym, List.map (merge_var var) flst)
    | Sum lst ->
      let res = List.fold_left (fun (v,lst) x -> match x with
        | Constant _ as cst -> (v, cst::lst)
        | Variable _ as var2 -> if var = var2 then(v +. 1.0 , lst) else (v, var2::lst)
        | Application (sym, flst) -> (v, Application(sym, List.map (merge_var var) flst)::lst)
        | Sum lst -> failwith "Sum should be flattenend"
        | Coeff (c, Application(sym, flst)) -> (v, Coeff(c, Application(sym, List.map (merge_var var) flst))::lst)
        | Coeff (c, Variable var2) as co -> if var = Variable var2 then (v +. c , lst) else (v, co::lst)
        | Coeff (_, Constant _) | Coeff(_, Sum _) | Coeff(_, Coeff _) -> failwith "merge_var: arg not normalized"
        ) (0.0, []) lst
      in Sum((Coeff (fst res, var))::(snd res))
    | Coeff (c, Application(sym, flst)) -> Coeff(c, Application(sym, List.map (merge_var var) flst))
    | Coeff _ as co -> co
  in
  let rec get_appl expr =
    match expr with
    | Constant _ -> []
    | Variable _ -> []
    | Application (sym, lst) as a -> List.fold_left (fun acc x -> OrdSet.union (get_appl x) acc) [a] lst
      (*a::(List.flatten (List.map get_appl lst))*)
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (get_appl x) acc) [] lst
      (*List.flatten (List.map get_appl lst)*)
    | Coeff (c,e) -> get_appl e
  in
  let rec merge_appl appl expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map (merge_appl appl) lst)
    | Sum lst ->
      let res = List.fold_left (fun (a,lst) x -> match x with
        | Constant _ as cst -> (a, cst::lst)
        | Variable _ as var -> (a, var::lst)
        | Application (sym, flst) ->
            let a2 = Application(sym, List.map (merge_appl appl) flst) in
              if a2 = appl then (a +. 1.0, lst) else (a, a2::lst)
        | Sum lst -> failwith "Sum should be flattenend"
        | Coeff (c, Application(sym, flst)) ->
            let a2 = Application(sym, List.map (merge_appl appl) flst) in
              if a2 = appl then (a +. c, lst) else (a, (Coeff(c,a2))::lst)
        | Coeff (c, Variable _) as co -> (a, co::lst)
        | Coeff (_, Constant _) | Coeff(_, Sum _) | Coeff(_, Coeff _)-> failwith "merge_var: arg not normalized"
        ) (0.0, []) lst
      in Sum((Coeff (fst res, appl))::(snd res))
    | Coeff (c, Application(sym, flst)) -> Coeff(c, Application(sym, List.map (merge_appl appl) flst))
    | Coeff _ as co -> co
  in
  let is_sum_relevant expr = match expr with
    | Constant 0.0 -> false
    | Coeff(0.0, _) -> false
    | _ -> true
  in
  let rec prune expr =
    match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map prune lst)
    | Sum lst ->
      begin
        let lst2 = List.filter is_sum_relevant lst in
        let lst3 = List.map prune lst2 in
          match List.length lst3 with
            | 0 -> Constant 0.0
            | 1 -> List.hd lst3
            | _ -> Sum (List.sort compare lst3)
      end
    | Coeff (c,e) ->
        if c = 0.0 then Constant 0.0
        else if c = 1.0 then prune e
        else Coeff(c, prune e)
  in
    Message.print Message.Debug (lazy("  original:    " ^ (print_expr expr)));
    let distr = distribute_coeff 1.0 expr in
      (*Message.print Message.Debug (lazy("  distributed: " ^ (print_expr distr)));*)
      let flat = flatten distr in
        (*Message.print Message.Debug (lazy("  flat:        " ^ (print_expr flat)));*)
        let cst = merge_cst flat in
          (*Message.print Message.Debug (lazy("  merge cst:   " ^ (print_expr cst)));*)
          let vars = get_var cst in
          let merged_var = List.fold_left (fun acc x -> merge_var x acc) cst vars in
            (*Message.print Message.Debug (lazy("  merge var:   " ^ (print_expr merged_var)));*)
            let pruned = prune merged_var in
              (*Message.print Message.Debug (lazy("  prune:       " ^ (print_expr pruned)));*)
              let apps = get_appl pruned in
              let merged_app =  List.fold_left (fun acc x -> merge_appl x acc) pruned apps in (*BUGGY: apps is not normalized ...*)
                (*Message.print Message.Debug (lazy("  merge app:   " ^ (print_expr merged_app)));*)
                let pruned2 = prune merged_app in
                  Message.print Message.Debug (lazy("  simple:      " ^ (print_expr pruned2)));
                  pruned2

(*TODO to have a simpler implementation, organize the simplify_expr like reduction rules of lambda calculus.
 * code would be easier to maintains (and less buggy), but it would be much slower
 *)
let rec normalize tree =
  match tree with
  | And ilst ->
    let new_lst =
      OrdSet.list_to_ordSet (
      List.filter (fun x -> x <> True) (
      List.fold_left
      ( fun acc x -> 
        match x with
        | And lst -> lst @ acc
        | _ -> x::acc
      )
      [] (List.map normalize ilst)))
    in
      if List.exists (fun x -> x = False) new_lst then
        False
      else
        begin
          match new_lst with
          | x::[] -> x
          | [] -> True
          | lst -> And lst
        end
  | Or ilst ->
    let new_lst =
      OrdSet.list_to_ordSet (
      List.fold_left
      ( fun acc x -> 
        match x with
        | Or lst -> lst @ acc
        | _ -> x::acc
      )
      [] (List.map normalize ilst))
    in 
      if List.exists (fun x -> x = True) new_lst then
        True
      else
        begin
          match (List.filter (fun x -> x <> False) new_lst) with
          | x::[] -> x
          | [] -> if new_lst = [] then True else False
          | lst -> Or lst
        end
  | Not i -> let n = normalize i in
    begin
      match n with
      | True -> False
      | False -> True
      | Lt (e1, e2) -> Leq(e2, e1)
      | Leq (e1, e2) -> Lt(e2, e1)
      | Not e -> e
      | _ as n -> Not n
    end
  | Eq (e1, e2) ->
    let (se1,se2) = (simplify_expr e1, simplify_expr e2) in 
    let c = compare se1 se2 in
      if c = 0 then True
      else if c <= 0 then Eq(se1, se2)
      else Eq (se2, se1)
  | Lt (Constant c1, Constant c2) ->
    if c1 < c2 then True else False
  | Lt (e1, e2) ->
    let (se1,se2) = (simplify_expr e1, simplify_expr e2) in 
      Lt(se1,se2)
  | Leq (Constant c1, Constant c2) ->
    if c1 <= c2 then True else False
  | Leq (e1, e2) ->
    let (se1,se2) = (simplify_expr e1, simplify_expr e2) in 
      Leq(se1,se2)
  | p -> p

let rec normalize_only pred = match pred with
  | And ilst ->
    let new_lst =
      OrdSet.list_to_ordSet (
      List.filter (fun x -> x <> True) (
      List.fold_left
      ( fun acc x -> 
        match x with
        | And lst -> lst @ acc
        | _ -> x::acc
      )
      [] (List.map normalize ilst)))
    in
      if List.exists (fun x -> x = False) new_lst then
        False
      else
        begin
          match new_lst with
          | x::[] -> x
          | [] -> True
          | lst -> And lst
        end
  | Or ilst ->
    let new_lst =
      OrdSet.list_to_ordSet (
      List.fold_left
      ( fun acc x -> 
        match x with
        | Or lst -> lst @ acc
        | _ -> x::acc
      )
      [] (List.map normalize ilst))
    in 
      if List.exists (fun x -> x = True) new_lst then
        True
      else
        begin
          match (List.filter (fun x -> x <> False) new_lst) with
          | x::[] -> x
          | [] -> if new_lst = [] then True else False
          | lst -> Or lst
        end
  | Not i -> let n = normalize i in
    begin
      match n with
      | True -> False
      | False -> True
      | Lt (e1, e2) -> Leq(e2, e1)
      | Leq (e1, e2) -> Lt(e2, e1)
      | Not e -> e
      | _ as n -> Not n
    end
  | rest -> rest


let rec order_eq eq = match eq with
  | And ilst -> And (List.map order_eq ilst)
  | Or ilst -> Or (List.map order_eq ilst)
  | Not i -> Not (order_eq i)
  | Eq (e1, e2) as eq ->
    let c = compare e1 e2 in
      if c = 0 then eq
      else if c <= 0 then Eq(e1, e2)
      else Eq (e2, e1)
  | p -> p

(*assume NNF*)
let is_conj_only p =
  let no_disj e = match e with
    | Or _ -> false
    | _ -> true
  in
    match p with
    | And lst -> List.for_all no_disj lst
    | Eq _ | Not _ | Lt _ | Leq _ | Atom _ | True | False -> true
    | _ -> false


(*assume NNF*)
let is_cnf formula =
  let rec contains_no_sub f = match f with
    | And _ | Or _ -> false
    | Not i -> contains_no_sub i
    | Eq _ | Leq _ | Lt _ | Atom _ | True | False -> true
  in
  let contains_or_no_sub f = match f with
    | And _ -> false
    | Or lst  -> List.for_all contains_no_sub lst
    | Not i -> contains_no_sub i
    | Eq _ | Leq _ | Lt _ | Atom _ | True | False -> true
  in
    match formula with
    | Or lst -> List.for_all contains_no_sub lst
    | And lst -> List.for_all contains_or_no_sub lst
    | _ -> true

let cnf tree =
  let rec process t = match t with
    | And lst -> List.flatten (List.map process lst)
    | Or lst ->
      let merge cnf1 cnf2 =
        List.flatten (List.map (fun x -> List.map (fun y -> x @ y) cnf2) cnf1)
      in
      let rec iterate acc l (*: list list list == disj of conj of disj *) =
        match l with
        | x :: xs -> iterate (merge x acc) xs
        | [] -> acc
      in
      let sub_cnf = List.map process lst in
        iterate [[]] sub_cnf
    | _ as t -> [[t]]
  in
    And (List.map (fun x -> Or x) (process tree))

(*TODO TEST*)
let dnf tree =
  let rec process t = match t with
    | Or lst -> List.flatten (List.map process lst)
    | And lst ->
      let merge dnf1 dnf2 =
        List.flatten (List.map (fun x -> List.map (fun y -> x @ y) dnf2) dnf1)
      in
      let rec iterate acc l (*: list list list == conj of disj of conj *) =
        match l with
        | x :: xs -> iterate (merge x acc) xs
        | [] -> acc
      in
      let sub_dnf = List.map process lst in
        iterate [[]] sub_dnf
    | _ as t -> [[t]]
  in
    Or (List.map (fun x -> And x) (process tree))


let rec simplify pred =  
  Message.print Message.Debug (lazy("  simplifing:  " ^ (print_pred pred)));
  let p = push_negation false pred in
    Message.print Message.Debug (lazy("  push:        " ^ (print_pred p)));
    let n = normalize p in
      Message.print Message.Debug (lazy("  normalize:   " ^ (print_pred n)));
      n

(**************************************)
module Expr =
  struct
    type t = expression
    let compare = compare
  end
module ExprSet = Set.Make(Expr)

module Pred =
  struct
    type t = predicate
    let compare = compare
  end
module PredSet = Set.Make(Pred)
(**************************************)

(** return the expressions of a predicate*)
let get_expr pred =
  let rec process pred = match pred with
    | False -> ExprSet.empty
    | True ->  ExprSet.empty
    | And lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process lst) 
    | Or lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process lst) 
    | Not p -> process p
    | Eq (e1,e2) -> ExprSet.add e2 (ExprSet.singleton e1)
    | Lt (e1,e2) -> ExprSet.add e2 (ExprSet.singleton e1)
    | Leq (e1,e2) -> ExprSet.add e2 (ExprSet.singleton e1)
    | Atom _ -> ExprSet.empty
  in
    ExprSet.fold (fun x acc -> x::acc) (process pred) []

let get_expr_deep pred =
  let rec process_expr expr = match expr with
    | Constant _ as c -> ExprSet.singleton c
    | Variable _ as v -> ExprSet.singleton v
    | Application (_, lst) as appl -> ExprSet.add appl (List.fold_left (fun acc x ->ExprSet.union acc (process_expr x)) ExprSet.empty lst)
    | Sum lst as sum -> ExprSet.add sum (List.fold_left (fun acc x ->ExprSet.union acc (process_expr x)) ExprSet.empty lst)
    | Coeff (c,e) as co ->ExprSet.add co (process_expr e)
  in
  let rec process_pred pred = match pred with
    | False -> ExprSet.empty
    | True ->  ExprSet.empty
    | And lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process_pred lst) 
    | Or lst -> List.fold_left (fun acc x -> ExprSet.union acc x) ExprSet.empty (List.map process_pred lst) 
    | Not p -> process_pred p
    | Eq (e1,e2) -> ExprSet.union (process_expr e1) (process_expr e2)
    | Lt (e1,e2) -> ExprSet.union (process_expr e1) (process_expr e2)
    | Leq (e1,e2) -> ExprSet.union (process_expr e1) (process_expr e2)
    | Atom _ -> ExprSet.empty
  in
    ExprSet.fold (fun x acc -> x::acc) (process_pred pred) []
  

(*OrdSet*)
let get_subterm pred =
  let rec process pred = match pred with
    | False -> []
    | True -> []
    | And lst as an -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [an] lst
    | Or lst as o -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [o] lst
    | Not p as n -> OrdSet.union [n] (process p)
    | Eq _ as eq -> [eq]
    | Lt _ as lt -> [lt]
    | Leq _ as leq -> [leq]
    | Atom _ as a -> [a]
  in
    process pred

let get_subterm_nnf pred =
  let rec process pred = match pred with
    | False -> []
    | True -> []
    | And lst as an -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [an] lst
    | Or lst as o -> List.fold_left (fun acc x -> OrdSet.union acc (process x)) [o] lst
    | Not _ as n -> [n] 
    | Eq _ as eq -> [eq]
    | Lt _ as lt -> [lt]
    | Leq _ as leq -> [leq]
    | Atom _ as a -> [a]
  in
    process pred

(*return the variables of a predicate*)
(*OrdSet*)
let get_var formula =
  let rec process_expr expr = match expr with
    | Constant _ -> []
    | Variable _ as v -> [v]
    | Application (_, lst) -> List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] lst
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] lst
    | Coeff (c,e) -> process_expr e
  in
  let expr = get_expr_deep formula in
    List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] expr

(*OrdSet*)
let get_fct_sym formula =
  let rec process_expr expr = match expr with
    | Constant _ -> []
    | Variable _ -> []
    | Application (f, lst) -> OrdSet.union [f] (List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc ) [] lst)
    | Sum lst -> List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] lst
    | Coeff (c,e) -> process_expr e
  in
  let expr = get_expr_deep formula in
    List.fold_left (fun acc x -> OrdSet.union (process_expr x) acc) [] expr

(*does the formula contains only given variable + constant term (no functions)*)
let only_vars vars formula =
  let rec only_vars_expr expr = match expr with
    | Constant _ -> true
    | Variable _ as v -> List.mem v vars
    | Application (_, _) -> false
    | Sum lst -> List.for_all only_vars_expr lst
    | Coeff (c,e) -> only_vars_expr e
  in
  let rec only_vars_pred formula = match formula with
    | And lst | Or lst -> List.for_all only_vars_pred lst
    | Not p -> only_vars_pred p
    | Eq (e1,e2) | Lt (e1,e2) | Leq (e1,e2) -> (only_vars_expr e1) && (only_vars_expr e2)
    | Atom _ -> false
    | _ -> true
  in
   only_vars_pred formula

(*does the formula contains only given variable, fct sym + constant term *)
let only_vars_and_symbols vars sym formula =
  let rec process_expr expr = match expr with
    | Constant _ -> true
    | Variable _ as v -> List.mem v vars
    | Application (f, lst) -> (List.mem f sym) && (List.for_all process_expr lst)
    | Sum lst -> List.for_all process_expr lst
    | Coeff (c,e) -> process_expr e
  in
  let rec process_pred formula = match formula with
    | And lst | Or lst -> List.for_all process_pred lst
    | Not p -> process_pred p
    | Eq (e1,e2) | Lt (e1,e2) | Leq (e1,e2) -> (process_expr e1) && (process_expr e2)
    | Atom _ -> false
    | _ -> true
  in
   process_pred formula

let only_expr expr formula =
  let rec process_pred formula = match formula with
    | And lst | Or lst -> List.for_all process_pred lst
    | Not p -> process_pred p
    | Eq (e1,e2) | Lt (e1,e2) | Leq (e1,e2) -> (List.mem e1 expr) && (List.mem e2 expr)
    | _ -> false
  in
   process_pred formula
(** return a formula in LI, in UIF, and a set of shared variable
 *  works only for the conjunctive fragment
 *  returns
 *      list of uif_preds (without And)
 *      list of li_preds  (without And)
 *      list of shared variables
 *      association list for the new variables: variable -> expression
 *)
let split_formula_LI_UIF pred =
  let counter = ref 0 in
  let expr_to_var = Hashtbl.create 13 in
  let defs = ref [] in
  let assoc = ref [] in
  (* allocate a new var if needed and the new definition*)
  let get_fresh_var expr = 
    try Hashtbl.find expr_to_var expr
    with Not_found ->
      begin
        counter := 1 + !counter;
        let v = Variable ("fresh_split_var"^(string_of_int !counter)) in
          Hashtbl.add expr_to_var expr v;
          defs := (order_eq (Eq(expr, v)))::!defs;
          assoc := (v,expr)::!assoc;
          v
      end
  in
  let rec process_e_li expr = match expr with
    | Constant _ as c -> c
    | Variable _ as v -> v
    | Application (sym, lst) -> (*UIF*)
      begin
        let uif_pure = Application (sym, List.map process_e_uif lst) in
          get_fresh_var uif_pure
      end
    | Sum lst -> Sum (List.map process_e_li lst)
    | Coeff (c,e) -> Coeff(c, process_e_li e)
  and process_e_uif expr = match expr with
    | Constant _ as c -> (*LI*) get_fresh_var c
    | Variable _ as v -> v
    | Application (sym, lst) -> Application(sym, List.map process_e_uif lst)
    | Sum lst -> (*LI*)
      begin
        let li_pure = Sum (List.map process_e_li lst) in
          get_fresh_var li_pure
      end
    | Coeff (c,e) -> (*LI*)
      begin
        let li_pure = Coeff (c, process_e_li e) in
          get_fresh_var li_pure
      end
  in
  let rec process_p pred = match pred with
    | And lst -> And (List.map process_p lst)
    | Not (Eq (e1,e2)) -> Not (Eq(process_e_uif e1, process_e_uif e2))(*UIF*)
    (*both side should have the same theory*)
    | Eq (e1,e2) ->
      begin
        let li = order_eq (Eq(process_e_li e1, process_e_li e2)) in
        let uif = order_eq (Eq(process_e_uif e1, process_e_uif e2)) in
          if li <> uif then defs := li::!defs;
          uif
      end
    | Lt (e1,e2) -> Lt(process_e_li e1, process_e_li e2)(*LI*)
    | Leq (e1,e2) -> Leq(process_e_li e1, process_e_li e2)(*LI*)
    | Atom _ -> failwith "separating theories: found Atom"
    | True -> (*True*) failwith "separating theories: found True"
    | False -> (*False*) failwith "separating theories: found False"
    | Or lst -> (*Or (List.map process_p lst)*) failwith "separating theories: found Or"
    | Not p -> failwith "separating theories: expect formula in NNF (Not)"
  in
  let keep_li pred = match pred with
    | And lst -> failwith "separating theories: found And"
    | Not (Eq _) -> false
    | Eq (e1,e2) ->(is_expr_LI e1) && (is_expr_LI e2)
    | Lt _ -> true
    | Leq _ -> true
    | Atom _ -> failwith "separating theories: found Atom"
    | True -> (*True*) failwith "separating theories: found True"
    | False -> (*False*) failwith "separating theories: found False"
    | Or lst -> (*Or (List.find query_fct lst)*) failwith "separating theories: found Or"
    | Not p -> failwith "separating theories: expect formula in NNF (Not)"
  in
  let keep_uif pred = match pred with
    | And lst -> failwith "separating theories: found And"
    | Not (Eq _) -> true
    | Eq (e1,e2) -> (is_expr_UIF e1) && (is_expr_UIF e2)
    | Lt _ -> false
    | Leq _ -> false
    | Atom _ -> failwith "separating theories: found Atom"
    | True -> (*True*) failwith "separating theories: found True"
    | False -> (*False*) failwith "separating theories: found False"
    | Or lst -> (*Or (List.find query_fct lst)*) failwith "separating theories: found Or"
    | Not p -> failwith "separating theories: expect formula in NNF (Not)"
  in
  (*Begin Here*)
  let p_lst = OrdSet.list_to_ordSet (match (process_p pred) with
    | And lst -> lst @ !defs
    | e -> e::!defs)
  in
  match (List.exists has_LI_only p_lst, List.exists has_UIF_only p_lst) with
  | (true, true) ->
    begin
      let uif_formula = List.filter keep_uif p_lst in
      let li_formula = List.filter keep_li p_lst in
      let var_uif = get_var (And uif_formula) in
      let var_li = get_var (And li_formula) in
      let shared_var = OrdSet.intersection var_uif var_li in
        (uif_formula, li_formula, shared_var, !assoc)
    end
  | (true, false) ->
    begin
      (*TODO assert ! assoc is emtpy*)
      ([], p_lst, [], !assoc)
    end
  | (false, true) ->
    begin
      (*TODO assert ! assoc is emtpy*)
      (p_lst, [], [], !assoc)
    end
  | (false, false) -> (*UIF arbirary choice*)
    begin
      (*TODO assert ! assoc is emtpy*)
      (p_lst, [], [], !assoc)
    end
