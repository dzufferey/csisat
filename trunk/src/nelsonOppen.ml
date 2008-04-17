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

(* return the unsat core for a formula
 * @param query_fct 'is_at' for a theory
 * @param fomula a formula of the theory in the conjunctive fragment
 * assume the theory in convex
 * raise SAT if the formula is not unsat.
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
    Message.print Message.Debug (lazy ("    with           "^(Utils.string_list_cat ", " (List.map AstUtil.print lst))));
    Message.print Message.Debug (lazy ("    fixed is       "^(Utils.string_list_cat ", " (List.map AstUtil.print fixed))));
    Message.print Message.Debug (lazy ("    unsat_core is  "^(Utils.string_list_cat ", " (List.map AstUtil.print !unsat_core))));
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
         Message.print Message.Debug (lazy("UNSAT core is: "^(AstUtil.print (And !unsat_core))));
         And !unsat_core
       end

(** Nelson Oppen for LI + UIF
 *  Assume the given formula is And [...] (job of sat solver)
 * TODO when to deduce, when to test for SAT ??
 *)
let is_liuif_sat formula =
  let new_eq = ref AstUtil.PredSet.empty in
  let (uif, li, shared, def) = AstUtil.split_formula_LI_UIF formula in
    Message.print Message.Debug (lazy("formula is "^(AstUtil.print formula)));
    Message.print Message.Debug (lazy("uif is "^(AstUtil.print (And uif))));
    Message.print Message.Debug (lazy("li  is "^(AstUtil.print (And li))));
    Message.print Message.Debug (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr shared))));
    Message.print Message.Debug (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> AstUtil.print (Eq (x,y))) def))));
  let possible_deduction = ref (
    OrdSet.list_to_ordSet (
      Utils.map_filter 
        ( fun (x, y) -> if x <> y then Some (AstUtil.order_eq (Eq (x,y))) else None)
        (OrdSet.cartesian_product shared shared)))
  in
  let graph = new SatUIF.dag (AstUtil.get_expr (And uif)) in
    ignore (graph#is_satisfiable (And uif));(*add the constraints*)

    let get_and_add_from_uif () =
      let from_uif_all = graph#new_equalities in
      let from_uif = List.filter (AstUtil.only_vars shared) from_uif_all in
        Message.print Message.Debug (lazy("new Eq ALL from UIF: "^(Utils.string_list_cat ", " (List.map AstUtil.print from_uif_all))));
        Message.print Message.Debug (lazy("new Eq from UIF: "^(Utils.string_list_cat ", " (List.map AstUtil.print from_uif))));
        List.iter (fun x -> new_eq := AstUtil.PredSet.add x !new_eq) from_uif
    in
    
    let rec try_and_propagate old_cardinal =
      let eq_deduced = AstUtil.PredSet.fold (fun x acc -> x::acc) !new_eq [] in
        Message.print Message.Debug (lazy("eq_deduced: "^(Utils.string_list_cat ", " (List.map AstUtil.print eq_deduced))));
        List.iter graph#add_constr eq_deduced;
        if graph#has_contradiction then false
        else
          begin
            (*propagate from UIF*)
            get_and_add_from_uif ();
            let eq_deduced = AstUtil.PredSet.fold (fun x acc -> x::acc) !new_eq [] in
            let full_li = And (eq_deduced @ li) in
              if SatLI.is_li_sat full_li then
                begin
                  (*
                  let to_test_full = graph#relevant_equalites in
                  let to_test = List.filter (AstUtil.only_vars shared) to_test_full in
                    Message.print Message.Debug ("Eq to test ALL from UIF: "^(Utils.string_list_cat ", " (List.map AstUtil.print to_test_full)));
                    Message.print Message.Debug ("Eq to test from UIF: "^(Utils.string_list_cat ", " (List.map AstUtil.print to_test)));
                  *)
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
                          if not (AstUtil.PredSet.mem x !new_eq) && (SatLI.is_eq_implied full_li x) then (*TODO bug testing useless thing*)
                            new_eq := AstUtil.PredSet.add x !new_eq
                          else
                            test_implied_eq xs
                        end
                      | [] -> ()
                    in
                    (*
                    let effective = List.filter (SatLI.is_eq_implied full_li) to_test in
                      List.iter (fun x -> new_eq := AstUtil.PredSet.add x !new_eq) effective;
                    *)
                      test_implied_eq to_test;
                      let new_cardinal = AstUtil.PredSet.cardinal !new_eq in
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

let remove_theory_split_var def eq =
  let rec find_equiv expr = match expr with
    | Application(s,lst) -> Application(s, List.map find_equiv lst)
    | e -> if List.mem_assoc e def then find_equiv (List.assoc e def) else e
  in
  let process eq = match eq with
    | Eq (e1,e2) -> AstUtil.order_eq (Eq (find_equiv e1, find_equiv e2))
    | Not (Eq (e1,e2)) -> AstUtil.order_eq (Eq (find_equiv e1, find_equiv e2))
    | _ -> failwith "remove_theory_split_var"
  in
    process eq

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
    | Eq (e1,e2) -> AstUtil.order_eq (Eq (find_equiv e1, find_equiv e2))
    | Not (Eq (e1,e2)) -> AstUtil.order_eq (Eq (find_equiv e1, find_equiv e2))
    | _ -> failwith "remove_theory_split_var"
  in
    process eq

(** Nelson Oppen for LI + UIF
 *  Assume the given formula is And [...] (job of sat solver)
 * @return (theory, eq)
 *      theory is LI | UIF | SATISFIABLE : LI or UIF indicate with part detected the unsatifiability
 *      eq is applied congruence or LA deduction
 * TODO when to deduce, when to test for SAT ??
 *)
let is_liuif_sat_with_eq formula =
  let li_eq = ref AstUtil.PredSet.empty in
  let uif_eq = ref AstUtil.PredSet.empty in
  let solver_eq = ref [] in (*~reversed proof*)
  let new_eq = ref AstUtil.PredSet.empty in
  let (uif, li, shared, def) = AstUtil.split_formula_LI_UIF formula in
    Message.print Message.Debug (lazy("formula is "^(AstUtil.print formula)));
    Message.print Message.Debug (lazy("uif is "^(AstUtil.print (And uif))));
    Message.print Message.Debug (lazy("li  is "^(AstUtil.print (And li))));
    Message.print Message.Debug (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr shared))));
    Message.print Message.Debug (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> AstUtil.print (Eq (x,y))) def))));
  let possible_deduction = ref (
    OrdSet.list_to_ordSet (
      Utils.map_filter 
        ( fun (x, y) -> if x <> y then Some (AstUtil.order_eq (Eq (x,y))) else None)
        (OrdSet.cartesian_product shared shared)))
  in
  let graph = new SatUIF.dag (AstUtil.get_expr (And uif)) in
  let uif_ded = graph#add_pred_with_applied (And uif) in(*add the constraints and get congruence*)
    List.iter
      (fun x -> 
        let clean = remove_theory_split_var def x in
          if not (AstUtil.PredSet.mem clean !uif_eq) then
            begin
              uif_eq := AstUtil.PredSet.add clean !uif_eq;
              solver_eq := (UIF, clean)::!solver_eq
            end
      ) uif_ded;

    let get_and_add_from_uif () =
      let from_uif_all = graph#new_equalities in
      let from_uif = List.filter (AstUtil.only_vars shared) from_uif_all in
        Message.print Message.Debug (lazy("new Eq ALL from UIF: "^(Utils.string_list_cat ", " (List.map AstUtil.print from_uif_all))));
        Message.print Message.Debug (lazy("new Eq from UIF: "^(Utils.string_list_cat ", " (List.map AstUtil.print from_uif))));
        List.iter (fun x -> new_eq := AstUtil.PredSet.add x !new_eq) from_uif
    in
    
    let rec try_and_propagate old_cardinal =
      let eq_deduced = AstUtil.PredSet.fold (fun x acc -> x::acc) !new_eq [] in
        Message.print Message.Debug (lazy("eq_deduced: "^(Utils.string_list_cat ", " (List.map AstUtil.print eq_deduced))));

        let uif_ded =  List.flatten (List.map (graph#add_constr_with_applied) eq_deduced) in(*add the constraints and get congruence*)
          List.iter
            (fun x -> 
              let clean = remove_theory_split_var def x in
                if not (AstUtil.PredSet.mem clean !uif_eq) then
                  begin
                    uif_eq := AstUtil.PredSet.add clean !uif_eq;
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
            let eq_deduced = AstUtil.PredSet.fold (fun x acc -> x::acc) !new_eq [] in
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
                          if not (AstUtil.PredSet.mem x !new_eq) && (SatLI.is_eq_implied full_li x) then (*TODO bug testing useless thing*)
                            begin
                              new_eq := AstUtil.PredSet.add x !new_eq;
                              let clean = remove_theory_split_var def x in
                                if not (AstUtil.PredSet.mem clean !li_eq) then
                                  begin
                                    li_eq := AstUtil.PredSet.add clean !li_eq; (*add LI decuction*)
                                    solver_eq := (LI, clean)::!solver_eq
                                  end
                            end
                          else
                            test_implied_eq xs
                        end
                      | [] -> ()
                    in
                      test_implied_eq to_test;
                      let new_cardinal = AstUtil.PredSet.cardinal !new_eq in
                      if new_cardinal - old_cardinal <= 0
                        then (SATISFIABLE, []) (*TODO*)
                        else try_and_propagate new_cardinal
                end
              else
                (LI, List.rev !solver_eq) (*sould not contains theory split var*)
        end
   in
     try_and_propagate 0




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
    | err -> failwith ("NelsonOppen, justifiy: "^(AstUtil.print err))
  and local_core deduction th eq =
    Message.print Message.Debug (lazy ("processing deduction "^(AstUtil.print eq)));
    let part_ded = previous_ded deduction eq [] in
      match th with
      | LI ->
        begin
          let uif_eq = snd (split_th [] [] part_ded) in
          let (contra1,contra2) = match eq with
            | Eq (e1,e2) -> (Lt(e1,e2),Lt(e2,e1))
            | err -> failwith ("NelsonOppen, local_core: "^(AstUtil.print err))
          in
          let core = SatLI.unsat_core (And (contra1::(uif_eq @ formula_li))) in
          let core1 = remove_el core contra1 in
          let core = SatLI.unsat_core (And (contra2::(uif_eq @ formula_li))) in
          let core2 = remove_el core contra2 in
          let core = AstUtil.normalize_only (And [core1;core2]) in
            Message.print Message.Debug (lazy ("partial (LA) core is "^(AstUtil.print core)));
            justifiy part_ded core
        end
      | UIF ->
        begin
          let li_eq = fst (split_th [] [] part_ded) in
          let core = SatUIF.unsat_core (And ((Not eq)::(li_eq @ formula_uif))) in
          let core = remove_el core (Not eq) in
            Message.print Message.Debug (lazy ("partial (UIF) core is "^(AstUtil.print core)));
            justifiy part_ded core
        end
      | _ -> failwith "NelsonOppen: unsat_core_NO-> local_core"
  in
  Message.print Message.Debug (lazy ("NO core for "^(AstUtil.print formula)));
  let full_core = match theory with
    | SATISFIABLE -> raise (SAT_FORMULA formula)
    | LI ->
      begin
        let uif_eq = snd (split_th [] [] eq_lst) in
        let core = SatLI.unsat_core (And (uif_eq @ formula_li)) in
          Message.print Message.Debug (lazy ("Last core (LA) is "^(AstUtil.print core)));
          AstUtil.normalize_only (justifiy eq_lst core)
      end
    | UIF ->
      begin
        let li_eq = fst (split_th [] [] eq_lst) in
        let core = SatUIF.unsat_core (And (li_eq @ formula_uif)) in
          Message.print Message.Debug (lazy ("Last core (EUF) is "^(AstUtil.print core)));
          AstUtil.normalize_only (justifiy eq_lst core)
      end
    | _ -> failwith "NelsonOppen: unsat_core_NO"
  in
    full_core

let unsat_core formula =
  match theory_of formula with
  | EUF ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      SatUIF.unsat_core formula (*overapprox: this is better but much slower: unsat_core_for_convex_theory SatUIF.is_uif_sat formula*)
    end
  | LA ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      SatLI.unsat_core formula
    end
  (*| EUF_LA -> unsat_core_for_convex_theory is_liuif_sat formula*)
  | EUF_LA ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      unsat_core_NO formula 
    end

let precise_unsat_core formula =
  match theory_of formula with
  | EUF ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      let core = SatUIF.unsat_core formula in(*overapprox: this is better but much slower: unsat_core_for_convex_theory SatUIF.is_uif_sat formula*)
        unsat_core_for_convex_theory SatUIF.is_uif_sat core
    end
  | LA ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      SatLI.unsat_core formula
    end
  (*| EUF_LA -> unsat_core_for_convex_theory is_liuif_sat formula*)
  | EUF_LA ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      let core = unsat_core_NO formula in
        unsat_core_for_convex_theory is_liuif_sat core
    end

let unsat_core_with_info formula =
  match theory_of formula with
  | EUF ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      let core = SatUIF.unsat_core formula in(*overapprox: this is better but much slower: unsat_core_for_convex_theory SatUIF.is_uif_sat formula*)
        match is_liuif_sat_with_eq core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (core, t, eq)
    end
  | LA ->  (*TODO better*)
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      let unsat_core = SatLI.unsat_core formula in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end
  | EUF_LA ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      let unsat_core = unsat_core_NO formula in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end

let precise_unsat_core_with_info formula =
  match theory_of formula with
  | EUF ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with EUF theory");
      let core = SatUIF.unsat_core formula in(*overapprox: this is better but much slower: unsat_core_for_convex_theory SatUIF.is_uif_sat formula*)
      let core = unsat_core_for_convex_theory SatUIF.is_uif_sat core in
        match is_liuif_sat_with_eq core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (core, t, eq)
    end
  | LA ->  (*TODO better*)
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA theory");
      let unsat_core = SatLI.unsat_core formula in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end
  | EUF_LA ->
    begin
      Message.print Message.Debug (lazy "UNSAT CORE with LA+EUF theory");
      let unsat_core = unsat_core_NO formula in
      let unsat_core = unsat_core_for_convex_theory is_liuif_sat unsat_core in
        match is_liuif_sat_with_eq unsat_core with
        | (SATISFIABLE, _) -> raise (SAT_FORMULA formula)
        | (t,eq) -> (unsat_core, t, eq)(*TODO is it possible to avoid calling is_liuif_sat_with_eq again ??*)
    end

(** assume the formula to be unsat
 *  assume a conjunction in NNF
 *)
let unsat_LIUIF conj =
  (*not covered => bool contradiction*)
  (*detect and directly add to cores*)
  let entailed = ref AstUtil.PredSet.empty in
  (*emulate SAT solver*)
  let rec process lst = match lst with
    | x::xs ->
      begin
        let contra = match x with
          | Not (Eq _ as eq) -> eq
          | Eq _ as eq -> Not eq
          | Lt (e1,e2) -> Leq (e2,e1)
          | Leq (e1,e2) -> Lt (e2, e1)
          | _ -> failwith "NelsonOppen: not normalized formula"
        in
          if AstUtil.PredSet.mem contra !entailed then
            begin
              Some (And [x;contra], BOOL, [])
            end
          else
            begin
              entailed := AstUtil.PredSet.add x !entailed;
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
            match is_liuif_sat_with_eq conj with
            | (SATISFIABLE, _) -> raise (SAT_FORMULA conj)
            | (t, eq) -> (conj, t, eq)
          end
      end
    | _ -> failwith "NelsonOppen: not a conjunction"
