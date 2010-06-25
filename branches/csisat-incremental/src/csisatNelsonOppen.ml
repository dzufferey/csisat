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

(** Nelson-Oppen theory combination.*)

open   CsisatAst
open   CsisatAstUtil
(**/**)
module Message = CsisatMessage
module Utils   = CsisatUtils
module OrdSet  = CsisatOrdSet
module SatLI   = CsisatSatLI
module SatUIF  = CsisatSatUIF
module TSolver = CsisatTheorySolver
(**/**)

(** Returns the unsat core for a formula (expensive).
 * Assumes the theory is convex.
 * @param query_fct 'is_sat' for a theory
 * @param fomula a formula of the theory in the conjunctive fragment
 * @raise SAT if the formula is not unsat.
 *)
let unsat_core_for_convex_theory query_fct formula =
  let lst = match formula with
    | And lst -> lst
    | True -> raise (SAT_FORMULA True)
    | Or _ -> failwith "unsat_core: only for the conjunctiv fragment"
    | Atom _ -> failwith "unsat_core: atom only for sat solver, PL is not convex."
    | el -> [el]
  in
  let unsat_core = ref [] in
  let rec divide_and_try fixed lst =
    Message.print Message.Debug (lazy "divide_and_try called: ");
    Message.print Message.Debug (lazy ("    with           "^(Utils.string_list_cat ", " (List.map print lst))));
    Message.print Message.Debug (lazy ("    fixed is       "^(Utils.string_list_cat ", " (List.map print fixed))));
    Message.print Message.Debug (lazy ("    unsat_core is  "^(Utils.string_list_cat ", " (List.map print !unsat_core))));
    (* assume query_fct (And (lst @ fixed @ !unsat_core)) is unsat *)
    let n = List.length lst in
      if n = 1 then
        begin (*one element and unsat -> in unsat core*)
          unsat_core := (List.hd lst) :: !unsat_core
        end
      else
        begin
          let (head, tail) = Utils.split_list (n/2) lst in
          (** the next line removes the part if there is no element of the unsat core in it*)
          let to_try =
            if not (query_fct (And (head @ !unsat_core @ fixed))) then
              [head]
            else if not (query_fct (And (tail @ !unsat_core @ fixed))) then
              [tail]
            else
              [head;tail]
          in
          let rec search lst = match lst with
            | x::[] -> divide_and_try fixed x
            | x::xs ->
              divide_and_try ((List.flatten xs) @ fixed) x;
              search xs
            | [] -> failwith "unsat_core_for_convex_theory: non convex theory ??"
          in
            search to_try
        end
   in 
     if query_fct (And lst) then
       raise (SAT_FORMULA formula)
     else
       begin
         divide_and_try [] lst;
         Message.print Message.Debug (lazy("UNSAT core is: "^(print (And !unsat_core))));
         And !unsat_core
       end

(** Nelson Oppen for LI + UIF.
 *  Assumes the given formula is And [...] (job of sat solver).
 *)
let is_liuif_sat formula =
  let new_eq = ref PredSet.empty in
  let (uif, li, shared, def) = split_formula_LI_UIF formula in
    Message.print Message.Debug (lazy("formula is "^(print formula)));
    Message.print Message.Debug (lazy("uif is "^(print (And uif))));
    Message.print Message.Debug (lazy("li  is "^(print (And li))));
    Message.print Message.Debug (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map print_expr shared))));
    (*Message.print Message.Debug (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> print (Eq (x,y))) def))));*)
  let possible_deduction = ref (
    OrdSet.list_to_ordSet (
      Utils.map_filter 
        ( fun (x, y) -> if x <> y then Some (order_eq (Eq (x,y))) else None)
        (Utils.cartesian_product shared shared)))
  in
  let graph = new SatUIF.dag (get_expr (And uif)) in
    ignore (graph#is_satisfiable (And uif));(*add the constraints*)

    let get_and_add_from_uif () =
      let from_uif_all = graph#new_equalities in
      let from_uif = List.filter (only_vars shared) from_uif_all in
        Message.print Message.Debug (lazy("new Eq ALL from UIF: "^(Utils.string_list_cat ", " (List.map print from_uif_all))));
        Message.print Message.Debug (lazy("new Eq from UIF: "^(Utils.string_list_cat ", " (List.map print from_uif))));
        List.iter (fun x -> new_eq := PredSet.add x !new_eq) from_uif
    in
    
    let rec try_and_propagate old_cardinal =
      let eq_deduced = PredSet.fold (fun x acc -> x::acc) !new_eq [] in
        Message.print Message.Debug (lazy("eq_deduced: "^(Utils.string_list_cat ", " (List.map print eq_deduced))));
        List.iter graph#add_constr eq_deduced;
        if graph#has_contradiction then false
        else
          begin
            (*propagate from UIF*)
            get_and_add_from_uif ();
            let eq_deduced = PredSet.fold (fun x acc -> x::acc) !new_eq [] in
            let full_li = And (eq_deduced @ li) in
              if SatLI.is_li_sat full_li then
                begin
                  possible_deduction := List.filter (graph#is_relevant_equality) !possible_deduction;
                  
                  (*test with one representant for each CC pair*)
                  let already_represented = ref [] in
                  let cc = graph#get_cc in
                  let expr_to_cc = Hashtbl.create (List.length cc) in
                    List.iter (fun cc -> List.iter (fun x -> Hashtbl.add expr_to_cc x cc) cc) cc;
                    let to_test = List.filter (fun x -> match x with
                        | Eq (e1,e2) ->
                          begin
                            let cc1 = Hashtbl.find expr_to_cc e1 in
                            let cc2 = Hashtbl.find expr_to_cc e2 in
                            let pair = if cc1 < cc2 then (cc1,cc2) else (cc2,cc1) in
                              if List.mem pair !already_represented then
                                false
                              else
                                begin
                                  already_represented := pair::!already_represented;
                                  true
                                end
                          end
                        | _ -> failwith "unreachable code" )
                      !possible_deduction
                    in
                    (*continue after the first successful test (TODO less eq_implied, but more is_li_sat -> is_it_better ??)*)
                    let rec test_implied_eq lst = match lst with
                      | x::xs ->
                        begin
                          if not (PredSet.mem x !new_eq) && (SatLI.is_eq_implied full_li x) then (*TODO bug testing useless thing*)
                            new_eq := PredSet.add x !new_eq
                          else
                            test_implied_eq xs
                        end
                      | [] -> ()
                    in
                      test_implied_eq to_test;
                      let new_cardinal = PredSet.cardinal !new_eq in
                      if new_cardinal - old_cardinal <= 0
                        then true
                        else try_and_propagate new_cardinal
                end
              else
                false
        end
   in
     try_and_propagate 0


type contradiction_in = LI
                      | UIF
                      | BOOL (*used elsewhere, TODO refactor*)
                      | SATISFIABLE

(*TODO what about LA (this handles only EUF)*)
let remove_theory_split_var def eq =
  let rec find_equiv expr = match expr with
    | Application(s,lst) -> Application(s, List.map find_equiv lst)
    | e -> if ExprMap.mem e def then find_equiv (ExprMap.find e def) else e
  in
  let process eq = match eq with
    | Eq (e1,e2) -> order_eq (Eq (find_equiv e1, find_equiv e2))
    | Not (Eq (e1,e2)) -> order_eq (Eq (find_equiv e1, find_equiv e2))
    | _ -> failwith "remove_theory_split_var"
  in
    process eq

(*
let put_theory_split_var def eq =
  let rev_def = List.map (fun (x,y) -> (y,x)) def in
  let rec find_equiv expr = match expr with
    | Application(s,lst) ->
      begin
        let e = Application(s, List.map find_equiv lst) in
          if List.mem_assoc e rev_def then find_equiv (List.assoc e rev_def) else e
      end
    | e -> if List.mem_assoc e rev_def then find_equiv (List.assoc e rev_def) else e
  in
  let process eq = match eq with
    | Eq (e1,e2) -> order_eq (Eq (find_equiv e1, find_equiv e2))
    | Not (Eq (e1,e2)) -> order_eq (Eq (find_equiv e1, find_equiv e2))
    | _ -> failwith "remove_theory_split_var"
  in
    process eq
*)

(** Nelson Oppen for LI + UIF.
 * Assumes the given formula is And [...] (job of sat solver).
 * @return (theory, eq) where
 *      theory is LI | UIF | SATISFIABLE : LI or UIF indicate with part detected the unsatifiability.
 *      eq is applied congruence or LA deduction.
 *)
let is_liuif_sat_with_eq formula =
  let li_eq = ref PredSet.empty in
  let uif_eq = ref PredSet.empty in
  let solver_eq = ref [] in (*~reversed proof*)
  let new_eq = ref PredSet.empty in
  let (uif, li, shared, def) = split_formula_LI_UIF formula in
    Message.print Message.Debug (lazy("formula is "^(print formula)));
    Message.print Message.Debug (lazy("uif is "^(print (And uif))));
    Message.print Message.Debug (lazy("li  is "^(print (And li))));
    Message.print Message.Debug (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map print_expr shared))));
    (*Message.print Message.Debug (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> print (Eq (x,y))) def))));*)
  let possible_deduction = ref (
    OrdSet.list_to_ordSet (
      Utils.map_filter 
        ( fun (x, y) -> if x <> y then Some (order_eq (Eq (x,y))) else None)
        (Utils.cartesian_product shared shared)))
  in
  let graph = new SatUIF.dag (get_expr (And uif)) in
  let uif_ded = graph#add_pred_with_applied (And uif) in(*add the constraints and get congruence*)
    List.iter
      (fun x -> 
        let clean = remove_theory_split_var def x in
          if not (PredSet.mem clean !uif_eq) then
            begin
              uif_eq := PredSet.add clean !uif_eq;
              solver_eq := (UIF, clean)::!solver_eq
            end
      ) uif_ded;

    let get_and_add_from_uif () =
      let from_uif_all = graph#new_equalities in
      let from_uif = List.filter (only_vars shared) from_uif_all in
        Message.print Message.Debug (lazy("new Eq ALL from UIF: "^(Utils.string_list_cat ", " (List.map print from_uif_all))));
        Message.print Message.Debug (lazy("new Eq from UIF: "^(Utils.string_list_cat ", " (List.map print from_uif))));
        List.iter (fun x -> new_eq := PredSet.add x !new_eq) from_uif
    in
    
    let rec try_and_propagate old_cardinal =
      let eq_deduced = PredSet.fold (fun x acc -> x::acc) !new_eq [] in
        Message.print Message.Debug (lazy("eq_deduced: "^(Utils.string_list_cat ", " (List.map print eq_deduced))));

        let uif_ded =  List.flatten (List.map (graph#add_constr_with_applied) eq_deduced) in(*add the constraints and get congruence*)
          List.iter
            (fun x -> 
              let clean = remove_theory_split_var def x in
                if not (PredSet.mem clean !uif_eq) then
                  begin
                    uif_eq := PredSet.add clean !uif_eq;
                    solver_eq := (UIF, clean)::!solver_eq
                  end
            ) uif_ded;
        
        
        if graph#has_contradiction then
          begin
              (UIF, List.rev !solver_eq) (*UIF contradiction*)
          end
        else
          begin
            (*propagate from UIF*)
            get_and_add_from_uif ();
            let eq_deduced = PredSet.fold (fun x acc -> x::acc) !new_eq [] in
            let full_li = And (eq_deduced @ li) in
              if SatLI.is_li_sat full_li then
                begin
                  possible_deduction := List.filter (graph#is_relevant_equality) !possible_deduction;
                  
                  (*test with one representant for each CC pair*)
                  let already_represented = ref [] in
                  let cc = graph#get_cc in
                  let expr_to_cc = Hashtbl.create (List.length cc) in
                    List.iter (fun cc -> List.iter (fun x -> Hashtbl.add expr_to_cc x cc) cc) cc;
                    let to_test = List.filter (fun x -> match x with
                        | Eq (e1,e2) ->
                          begin
                            let cc1 = Hashtbl.find expr_to_cc e1 in
                            let cc2 = Hashtbl.find expr_to_cc e2 in
                            let pair = if cc1 < cc2 then (cc1,cc2) else (cc2,cc1) in
                              if List.mem pair !already_represented then
                                false
                              else
                                begin
                                  already_represented := pair::!already_represented;
                                  true
                                end
                          end
                        | _ -> failwith "unreachable code" )
                      !possible_deduction
                    in
                    (*continue after the first successful test (TODO less eq_implied, but more is_li_sat -> is_it_better ??)*)
                    let rec test_implied_eq lst = match lst with
                      | x::xs ->
                        begin
                          if not (PredSet.mem x !new_eq) && (SatLI.is_eq_implied full_li x) then (*TODO bug testing useless thing*)
                            begin
                              new_eq := PredSet.add x !new_eq;
                              let clean = remove_theory_split_var def x in
                                if not (PredSet.mem clean !li_eq) then
                                  begin
                                    li_eq := PredSet.add clean !li_eq; (*add LI decuction*)
                                    solver_eq := (LI, clean)::!solver_eq
                                  end
                            end
                          else
                            test_implied_eq xs
                        end
                      | [] -> ()
                    in
                      test_implied_eq to_test;
                      let new_cardinal = PredSet.cardinal !new_eq in
                      if new_cardinal - old_cardinal <= 0
                        then (SATISFIABLE, []) (*TODO*)
                        else try_and_propagate new_cardinal
                end
              else
                (LI, List.rev !solver_eq) (*sould not contains theory split var*)
        end
   in
     try_and_propagate 0



(** unsat core for LA + EUF. *)
let unsat_core_NO formula =
  let rec split_th accLI accUIF lst = match lst with
    | (LI, eq)::xs -> split_th (eq::accLI) accUIF xs
    | (UIF, eq)::xs -> split_th accLI (eq::accUIF) xs
    | [] -> (accLI, accUIF)
    | _ -> failwith "NelsonOppen: unsat_core_NO -> split_th"
  in
  let rec is_deduction ded eq = match ded with
    | (th, d)::xs when d=eq -> Some th
    | _::xs -> is_deduction xs eq
    | [] -> None
  in
  let formula_lst = match formula with
    | And lst -> lst
    | el -> [el] 
  in
  let formula_li = List.filter (fun x -> match x with | Not _ -> false | _ -> true) formula_lst in
  let formula_uif = List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) formula_lst in
  let remove_el conj el = match conj with
    | And lst -> And (List.filter (fun x -> x<>el) lst)
    | _ -> failwith "NelsonOppen, unsat_core_NO: unsat core should be a conj"
  in
  let rec previous_ded ded eq acc = match ded with
    | (_, d)::xs when d=eq -> List.rev acc
    | x::xs -> previous_ded xs eq (x::acc)
    | [] -> failwith "NelsonOppen, previous_ded: did not even found given deduction"
  in
  let (theory, eq_lst) = is_liuif_sat_with_eq formula in
  let rec justifiy deduction formula = match formula with (*TODO can loop ?? (circular proof)*)
    | And lst -> And (List.map (justifiy deduction) lst) 
    | Eq _ as eq ->
      begin
        match is_deduction deduction eq with
        | Some dth -> local_core deduction dth eq
        | None -> eq
      end
    | Not _ as neq -> neq
    | Lt _ as lt -> lt
    | Leq _ as leq -> leq
    | err -> failwith ("NelsonOppen, justifiy: "^(print err))
  and local_core deduction th eq =
    Message.print Message.Debug (lazy ("processing deduction "^(print eq)));
    let part_ded = previous_ded deduction eq [] in
      match th with
      | LI ->
        begin
          let uif_eq = snd (split_th [] [] part_ded) in
          let (contra1,contra2) = match eq with
            | Eq (e1,e2) -> (Lt(e1,e2),Lt(e2,e1))
            | err -> failwith ("NelsonOppen, local_core: "^(print err))
          in
          let core = SatLI.unsat_core (And (contra1::(uif_eq @ formula_li))) in
          let core1 = remove_el core contra1 in
          let core = SatLI.unsat_core (And (contra2::(uif_eq @ formula_li))) in
          let core2 = remove_el core contra2 in
          let core = normalize_only (And [core1;core2]) in
            Message.print Message.Debug (lazy ("partial (LA) core is "^(print core)));
            justifiy part_ded core
        end
      | UIF ->
        begin
          let li_eq = fst (split_th [] [] part_ded) in
          let core = SatUIF.unsat_core (And ((Not eq)::(li_eq @ formula_uif))) in
          let core = remove_el core (Not eq) in
            Message.print Message.Debug (lazy ("partial (UIF) core is "^(print core)));
            justifiy part_ded core
        end
      | _ -> failwith "NelsonOppen: unsat_core_NO-> local_core"
  in
  Message.print Message.Debug (lazy ("NO core for "^(print formula)));
  let full_core = match theory with
    | SATISFIABLE -> raise (SAT_FORMULA formula)
    | LI ->
      begin
        let uif_eq = snd (split_th [] [] eq_lst) in
        let core = SatLI.unsat_core (And (uif_eq @ formula_li)) in
          Message.print Message.Debug (lazy ("Last core (LA) is "^(print core)));
          normalize_only (justifiy eq_lst core)
      end
    | UIF ->
      begin
        let li_eq = fst (split_th [] [] eq_lst) in
        let core = SatUIF.unsat_core (And (li_eq @ formula_uif)) in
          Message.print Message.Debug (lazy ("Last core (EUF) is "^(print core)));
          normalize_only (justifiy eq_lst core)
      end
    | _ -> failwith "NelsonOppen: unsat_core_NO"
  in
    full_core

(** unsat core for LA + EUF.
 * Uses NO only if needed.
 *)
let unsat_core formula =
  match theory_of formula with
  | [EUF] | [] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      SatUIF.unsat_core formula 
    end
  | [LA] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      SatLI.unsat_core formula
    end
  | [EUF;LA] | [LA;EUF] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      unsat_core_NO formula 
    end
  | _ -> failwith "NO unsupported theories"

let precise_unsat_core formula =
  match theory_of formula with
  | [EUF] | [] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      let core = SatUIF.unsat_core formula in
        unsat_core_for_convex_theory SatUIF.is_uif_sat core
    end
  | [LA] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      SatLI.unsat_core formula
    end
  | [EUF;LA] | [LA;EUF] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      let core = unsat_core_NO formula in
        unsat_core_for_convex_theory is_liuif_sat core
    end
  | _ -> failwith "NO unsupported theories"

(**
 * @return the unsat core, theory that finds the contradiction, list of deduced equalities.
 *)
let unsat_core_with_info formula =
  match theory_of formula with
  | [EUF] | [] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      let core = SatUIF.unsat_core formula in
        match is_liuif_sat_with_eq core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (core, t, eq)
    end
  | [LA] ->  (*TODO better*)
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      let unsat_core = SatLI.unsat_core formula in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end
  | [EUF;LA] | [LA;EUF] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      let unsat_core = unsat_core_NO formula in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end
  | _ -> failwith "NO unsupported theories"

(** Like unsat_core_with_info but more precise, and more expensive. *)
let precise_unsat_core_with_info formula =
  match theory_of formula with
  | [EUF] | [] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      let core = SatUIF.unsat_core formula in(*overapprox: this is better but much slower: unsat_core_for_convex_theory SatUIF.is_uif_sat formula*)
      let core = unsat_core_for_convex_theory SatUIF.is_uif_sat core in
        match is_liuif_sat_with_eq core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (core, t, eq)
    end
  | [LA] ->  (*TODO better*)
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      let unsat_core = SatLI.unsat_core formula in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end
  | [EUF;LA] | [LA;EUF] ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      let unsat_core = unsat_core_NO formula in
      let unsat_core = unsat_core_for_convex_theory is_liuif_sat unsat_core in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end
  | _ -> failwith "NO unsupported theories"

(** Special fct with catch of boolean contradiction.
 *  This method is used when bypassing the satsolver (conjunction only).
 *  Assumes the formula to be unsat.
 *  Assumes a conjunction in NNF.
 *)
let unsat_LIUIF conj =
  (*not covered => bool contradiction*)
  (*detect and directly add to cores*)
  let entailed = ref PredSet.empty in
  (*emulate SAT solver*)
  let rec process lst = match lst with
    | x::xs ->
      begin
        let contra = match x with
          | Not (Eq _ as eq) -> eq
          | Eq _ as eq -> Not eq
          | Lt (e1,e2) -> Leq (e2,e1)
          | Leq (e1,e2) -> Lt (e2, e1)
          | Atom (External _) as a -> Not a
          | Not (Atom (External _) as a) -> a
          | e -> failwith ("NelsonOppen: not normalized formula, found: "^( print e))
        in
          if PredSet.mem contra !entailed then
            begin
              Some (And [x;contra], BOOL, [])
            end
          else
            begin
              entailed := PredSet.add x !entailed;
              process xs
            end
      end
    | [] -> None
  in
    match conj with
    | And lst ->
      begin
        match process lst with
        | Some x -> x
        | None ->
          begin
            let externals = get_external_atoms conj in
            let conj = remove_atoms conj in
            if conj = True then (*when only atoms*)
              raise (SAT_FORMULA (normalize_only (And externals)))
            else
              match is_liuif_sat_with_eq conj with
              | (SATISFIABLE, _) -> 
                raise (SAT_FORMULA (normalize_only (And [conj; And externals])))
              | (t, eq) -> (conj, t, eq)
          end
      end
    | _ -> failwith "NelsonOppen: not a conjunction"

(* TODO now the core solver takes care of the Ts
module NOSolver(T1: TSolver.TheorySolver)(T2: TSolver.TheorySolver) =
  struct

    type events = PropagationT1toT2 of (predicate list)
                | PropagationT2toT1 of (predicate list)
                | Added of predicate * (predicate option)(*added to t1*) * (predicate option)(*added to t2*)
    
    (*TODO keep a dag of equality on shared variables for the propagation ... *)
    type t = {
      t1: T1.t;
      t2: T2.t;
      dag: SatUIF.Dag.t;
      shared: expression list;
      var_to_expr: expression ExprMap.t;
      propagations: events Stack.t
    }

    (** Creates a new solver, initially without constraints.
     * @param list of all potential predicates (for T-propagation) *)
    let create pred_set =
      if List.exists (fun x -> List.mem x T2.theory) T1.theory
      then failwith "NOSolver the two solvers handle theories that intersect";
      let (t1_formula, t2_formula, shared, var_to_expr) = split_formula_t1_t2 T1.theory T2.theory (And (PredSet.elements pred_set)) in
      (*keep a dag of equalities only when there are shared variables*)
      let dag =
        if List.length shared > 1 then
          begin
            let (_, pred_shared) = List.fold_left
                (fun (e1, acc) e2 -> (e2, PredSet.add (order_eq (Eq (e1,e2))) acc))
                (List.hd shared, PredSet.empty)
                (List.tl shared)
            in
              SatUIF.Dag.create pred_shared
          end
        else SatUIF.Dag.create PredSet.empty
      in
        { t1 = T1.create (predSet_of_list t1_formula);
          t2 = T2.create (predSet_of_list t2_formula);
          dag = dag;
          shared = shared;
          var_to_expr = var_to_expr;
          propagations = Stack.create () }

    let push t pred =
      (*TODO makes the predicate belongs to t1 and/or t2
       * what if one side is empty ???
       * then push and propagate ...
       * propagations are also put in the dag
       *)
      if not (is_sat t) then failwith "NOSolver: push called on an already unsat system.";
      let rev_defs = failwith "TODO" in
      let with_vars = put_theory_split_variables rev_defs pred in
      let (t1_pred, t2_pred) = failwith "TODO" in
      let sat1, t1_prop = Utils.maybe (fun p -> let res = T1.push t.t1 p in (res, T1.propagation t.t1 t.shared)) (lazy (true ,[])) t1_pred in
        if not sat1 then
          begin
            Stack.push (Added (pred, t1_pred, None)) t.propagations;
            false
          end
        else
          let sat2, t2_prop = Utils.maybe (fun p -> let res = T2.push t.t2 p in (res, T2.propagation t.t2 t.shared)) (lazy (true,[])) t2_pred in
            if not sat2 then
              begin
                Utils.maybe (fun _ -> T1.pop t.t1) (lazy ()) t1_pred;
                Stack.push (Added (pred, None, t2_pred)) t.propagations;
                false
              end
            else
              begin
                let t1_queue = Queue.create () in
                let t2_queue = Queue.create () in
                let rec propagates_t
                    queue mk_event push prop_t
                    other_queue other_mk_event other_push other_prop_t
                    acc =
                  let same_propagates = propagates_t
                    queue mk_event push prop_t
                    other_queue other_mk_event other_push other_prop_t
                  in
                  let other_propagates = propagates_t
                    other_queue other_mk_event other_push other_prop_t
                    queue mk_event push prop_t
                  in
                  if not (Queue.is_empty queue) then
                    begin
                      let p = Queue.take queue in
                        SatUIF.Dag.push t.dag p;
                        if push p then 
                          begin
                            List.iter (fun x -> Queue.add x queue) (prop_t ());
                            same_propagates (p::acc)
                          end
                        else
                          begin
                            Stack.push (mk_event (p::acc)) t.propagations;
                            false
                          end
                    end
                  else
                    begin
                      Stack.push (mk_event acc) t.propagations;
                      if not (Queue.is_empty other_queue) then other_propagates [] else true
                    end
                in
                  List.iter (fun p -> Queue.add p t1_queue) t1_prop;
                  List.iter (fun p -> Queue.add p t2_queue) t2_prop;
                  propagates_t
                    t1_queue (fun lst -> PropagationT1toT2 lst) (T2.push t.t2) (fun () -> T2.propagation t.t2 t.shared)
                    t2_queue (fun lst -> PropagationT2toT1 lst) (T1.push t.t1) (fun () -> T1.propagation t.t1 t.shared)
                    []
              end
    
    let pop t =
      let rec inspect_stack () = 
        if Stack.is_empty t.propagations then
          failwith "NOSolver: pop called on an empty stack"
        else
          begin
            match Stack.pop t.propagations with
            | PropagationT1toT2 lst -> List.iter (fun _ -> T2.pop t.t2; SatUIF.Dag.pop t.dag) lst; inspect_stack ()
            | PropagationT2toT1 lst -> List.iter (fun _ -> T1.pop t.t1; SatUIF.Dag.pop t.dag) lst; inspect_stack ()
            | Added (_, added_to_t1, added_to_t2) ->
              Utils.maybe (fun _ -> T1.pop t.t1) (lazy ()) added_to_t1;
              Utils.maybe (fun _ -> T2.pop t.t2) (lazy ()) added_to_t2
          end
      in
        inspect_stack ()
  end
*)