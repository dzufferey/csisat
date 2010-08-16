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
 * always handles the EUF theory,
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
module SatEUF  = CsisatSatEUF
module Node    = CsisatSatEUF.Node
(**/**)

type change = StackSat of predicate (* predicate given by sat solver *)
            | StackNO of predicate * theory
            | StackChanges of (theory * predicate) list (*what was sent to which theory*)
type explanation = ProofEUF of SatEUF.congruence_proof
                 | ProofDL of predicate (*TODO more complex *)
                 | NoProof (*TODO remove when everything is done *)

let string_of_explanation e = match e with
  | ProofEUF path -> SatEUF.string_of_proof path
  | _ -> "TODO"

type t = {
  sat_solver: Dpll.csi_dpll;
  propositions: PredSet.t;
  stack: change Stack.t;
  mutable explanations: (predicate * theory * explanation list) PredMap.t;
  (* about the equisatisfiable conversion *)
  dico: (predicate, predicate) Hashtbl.t;
  pred_to_atom: (predicate, predicate) Hashtbl.t;
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

(* method 'shortcuts' *)
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
  Message.print Message.Debug (lazy("CoreSolver: EUF assignment is "^(String.concat ", " (List.map print_pred (SatEUF.current_predicates t.euf)))));
  Message.print Message.Debug (lazy("CoreSolver: full core is "^(print_pred core)));
  let (no_to_justify, core) = split_shared_NO (normalize_only (And [pred; core])) in
  Message.print Message.Debug (lazy("CoreSolver: contradiction in "^(string_of_theory th)^" with " ^ (print_pred pred)));
  Message.print Message.Debug (lazy("CoreSolver: given core is "^(print_pred (And core))));
  Message.print Message.Debug (lazy("CoreSolver: deductions are "^(String.concat ", " (List.map (fun (a,b) -> (print_pred a)^"("^(string_of_theory b)^")") deductions))));
  Message.print Message.Debug (lazy("CoreSolver: NO to justify are "^(String.concat ", " (List.map (fun (a,b) -> (print_pred a)^" ("^(string_of_theory b)^")") no_to_justify))));
  let (_, core') = justify_list PredSet.empty PredSet.empty no_to_justify in
  let full_core = normalize (And (core @ (PredSet.elements core'))) in
  let explanation =
    if th = EUF && no_to_justify = []
    then [ProofEUF (SatEUF.mk_proof t.euf (contra pred))]
    else [NoProof] (*TODO explanation: needs to accumulate deductions (for later interpolation)*)
  in
    (full_core, pred, th, explanation)

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
            | Unsat of DpllProof.res_proof * (predicate * theory * explanation list) PredMap.t

let solved_to_string t prf = match prf with
  | Sat lst ->
    begin
      let lst = (List.filter (fun x -> x <> True) (List.map remove_equisat_atoms lst)) in
      "Satisfiable: " ^ (String.concat ", " (List.map print_pred lst))
    end
  | Unsat (res, blocking_clauses) ->
    begin
      let (str_prf, (_,index_to_atom, clauses)) = DpllProof.tracecheck_of_proof_with_tables res in
      let blocking_clause pred (contradiction, th, explanation) =
        (print_pred (normalize_only (unabstract_equisat t.dico (Not pred)))) ^ " is unsat ("^(string_of_theory th)^","^(print_pred contradiction)^") because:\n" ^ 
        (String.concat "\n" (List.map string_of_explanation explanation)) ^ "\n"
      in
      let clause set = print_pred (Or (List.map (unabstract_equisat t.dico) (PredSet.elements set))) in
      let prop_buffer = Buffer.create 1000 in
      let clause_buffer = Buffer.create 1000 in
      let blocking_buffer = Buffer.create 1000 in
        Hashtbl.iter (fun k v -> Buffer.add_string prop_buffer ((string_of_int k) ^ " -> " ^ (print_pred (unabstract_equisat t.dico v)) ^ "\n")) index_to_atom;
        Hashtbl.iter (fun k v -> Buffer.add_string clause_buffer ((string_of_int v) ^ " -> " ^ (clause k) ^ "\n")) clauses;
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
  
  (* equisatisfiable *)
  let dico, pred_to_atom, f =
    if is_cnf pred then (Hashtbl.create 0, Hashtbl.create 0, pred)
    else better_equisatisfiable pred (*TODO more tests for better_equisatisfiable !!*)
  in

  let graph = {
      sat_solver = sat_solver;
      propositions = pset;
      stack = stack;
      explanations = PredMap.empty;
      dico = dico;
      pred_to_atom = pred_to_atom;
      shared = shared;
      definitions = definitions;
      rev_definitions = ExprMap.fold (fun k v acc -> ExprMap.add v k acc) definitions ExprMap.empty;
      euf = euf;
      dl = dl_solver
    }
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
