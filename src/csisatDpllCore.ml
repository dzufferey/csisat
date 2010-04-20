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

(** Part of the DPLL: Core (decision policy,...) *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatSatInterface
open   CsisatDpllClause
open   CsisatDpllProof
open   CsisatUtils
(**/**)
module Message = CsisatMessage
module OrdSet  = CsisatOrdSet
module Global  = CsisatGlobal
(**/**)

(*a simple dpll SAT solver*)
(*TODO improve the learning (less clause)
*)

(** Resolution proof*)
type int_res_proof = IRPNode of int * int_res_proof * int_res_proof * clause (** pivot, left, right, result*)
                   | IRPLeaf of clause (** A leaf is simply a clause.*)
let int_get_result proof = match proof with
  | IRPNode (_,_,_,r) -> r
  | IRPLeaf r -> r

(** To store the decision level. *)
type var_assign = Open (** free choice (decision policy) *)
                | Implied of int_res_proof (** unit resolution*)
                | TImplied of int_res_proof (** implied by a theory (bool+T) TODO *)
(* for partial solving *)
type int_status = IAffected of int list
                | IAffectation of int list * int list (* newly affected + full affectation that satifies the system *)
                | IBacktracked of int (*how many atoms where set to Unk*)
                | IProof of int_res_proof option (* unsat: return resolution proof if asked *)

class system =
  fun with_prf ->
  object (self)

    val keep_proof = with_prf
    val mutable possibly_sat = true
    val mutable resolution_proof = None
    
    val mutable clauses = Array.make 0 (new clause 1 [1] true )
    val mutable assignment = Array.make 2 lUnk
    val choices = Stack.create ()
    val mutable decision_level = 0
    val mutable unsat_clauses = IntSet.empty
    val mutable prop_to_clauses = Array.make 2 (IntSet.empty, IntSet.empty)
    val mutable learning_level = 1
    val partial_proof = Hashtbl.create 1000

    method get_assigned_props =
      begin
        let affect = ref [] in
          Array.iteri (fun i x -> if x <> lUnk then affect := i :: !affect) assignment;
          !affect
      end
    method get_assign = List.map (fun i -> i * assignment.(i)) self#get_assigned_props
    
    method get_decision_level = decision_level

    (** 0-: no learning,
     *  1+: learn clause that are less or equal than value.
     * Default value is 3/2 * average size.
     * Warning: call this method after having called init.
     *)
    method set_learning_level l = learning_level <- l
    
    method private store_proof clause proof = Hashtbl.replace partial_proof clause proof
    method private get_partial_proof clause = Hashtbl.find partial_proof clause
    method private proof_for_clause clause =
      if clause#is_learned then self#get_partial_proof clause
      else IRPLeaf clause


    method resize max_index =
      let size = (Array.length assignment) -1 in
        Message.print Message.Debug
          (lazy("DPLL, resizing from "^(string_of_int size)^" to "^(string_of_int max_index)));
        if max_index <> size then
          begin
            if max_index < size then
              begin
                for i = max_index + 1 to size do
                  assert (Global.is_off_assert() || assignment.(i) = lUnk);
                  assert (Global.is_off_assert() || prop_to_clauses.(i) = (IntSet.empty, IntSet.empty))
                done
              end;
            Message.print Message.Debug (lazy("DPLL, resizing clauses"));
            Array.iter (fun x -> x#resize max_index) clauses;

            Message.print Message.Debug (lazy("DPLL, resizing assignment"));
            let new_array = Array.make (max_index + 1) lUnk in
              Array.blit assignment 1 new_array 1 (min max_index size);
              assignment <- new_array;
              
              Message.print Message.Debug (lazy("DPLL, resizing prop_to_clauses"));
              let new_prop_to_clause =  Array.make (max_index + 1) (IntSet.empty, IntSet.empty) in
                Array.blit prop_to_clauses 1 new_prop_to_clause 1 (min max_index size);
                prop_to_clauses <- new_prop_to_clause
          end
    
    method private add_to_prop_to_clause index cl =
      let pos = cl#get_pos_props in
      let neg = cl#get_neg_props in
        IntSet.iter (fun p ->
            let (old_p,old_n) = prop_to_clauses.(p) in
            let new_p = IntSet.add index old_p in
              prop_to_clauses.(p) <- (new_p,old_n)
          ) pos;
        IntSet.iter (fun n ->
            let (old_p,old_n) = prop_to_clauses.(n) in
            let new_n = IntSet.add index old_n in
              prop_to_clauses.(n) <- (old_p,new_n)
          ) neg

    method init (formula: int list list) =
      Message.print Message.Debug (lazy("DPLL, init"));
      (* clauses *)
      let size = (Array.length assignment -1) in
      Message.print Message.Debug (lazy("DPLL, create clauses"));
      let clauses_lst = List.map (fun x -> new clause size x false) formula in
        clauses <- Array.of_list clauses_lst;
      Message.print Message.Debug (lazy("DPLL, add_to_prop_to_clause"));
        Array.iteri (fun i c -> self#add_to_prop_to_clause i c) clauses;
        (* unsat_clauses *)
        let nb_clauses = Array.length clauses in
        let enum = ref IntSet.empty in
          for i = 0 to nb_clauses -1 do
            enum := IntSet.add i !enum
          done;
          unsat_clauses <- !enum;
          (* clause learning *)
          let cl_size = List.map List.length formula in
          let average_size = (List.fold_left (+) 0 cl_size) / nb_clauses in
            self#set_learning_level ((3 * average_size) / 2);
      Message.print Message.Debug (lazy("DPLL, initialized"))
    
    method reset =
      possibly_sat <- true;
      resolution_proof <- None;
      clauses <-  Array.make 0 (new clause 1 [1] true );
      assignment <- Array.make 1 lUnk;
      Stack.clear choices;
      decision_level <- 0;
      learning_level <- 1;
      unsat_clauses <- IntSet.empty;
      prop_to_clauses <- Array.make 0 (IntSet.empty, IntSet.empty);
      Hashtbl.clear partial_proof

    (** insert a new clause
     * @return false if need to backtrack
     *)
    method private new_clause cl =
      List.iter (cl#affect) self#get_assign;
      clauses <- Array.append clauses (Array.make 1 cl);
      let last_index = (Array.length clauses) -1 in
        self#add_to_prop_to_clause last_index cl;
        if cl#is_sat then
          begin
            (*unstack to the first lit that satisfied the clause*)
            let rec insert sat_element =
              let (pivot,reason,clauses) as entry = Stack.pop choices in
                if pivot = sat_element then
                  begin
                    assert (Global.is_off_assert() || cl#has pivot);
                    Stack.push (pivot, reason, IntSet.add last_index clauses) choices
                  end
                else
                  begin
                    insert sat_element;
                    Stack.push entry choices
                  end
            in
              insert (cl#get_satisfied);
              true
          end
        else
          begin
            unsat_clauses <- IntSet.add last_index unsat_clauses;
            not (cl#contradiction)
          end

    method add_clause (lst: int list) =
      let size = (Array.length assignment) -1 in
      let cl = new clause size lst false in
      let res = self#new_clause cl in
        if not res then self#backjump cl
    
    (*TODO
     * -is subset of an existing clause ?
     * -is stronger than an existing clause ?
     * => using some kind of tries ( O(#literals) )??
     *)
    method private choose_to_learn_clause cl prf =
      if cl#full_size <= learning_level then
        begin
          (* as learning is not only at the end, new_clause may return false *)
          ignore (self#new_clause cl);
          self#store_proof cl prf
        end

    (** Method to call at the end of the backtracking.
     *  It forces the learning of the given clause.
     *  The learned clause has to be in a not contradictory state.
     *)
    method private force_learning cl prf =
      let res = self#new_clause cl in
        assert (Global.is_off_assert() || res);
        self#store_proof cl prf

    method affect p reason =
      Message.print Message.Debug (lazy("DPLL, affecting : "^(string_of_int p)));
      assert (Global.is_off_assert() || assignment.(index_of_literal p) = lUnk);
      assignment.(index_of_literal p) <- value_of_literal p;
      let (pos,neg) = prop_to_clauses.(index_of_literal p) in
      let (_true,_false) = if (value_of_literal p) = lTrue then (pos,neg) else (neg,pos)
      in
      let newly_sat = IntSet.filter (fun i -> not (clauses.(i))#is_sat) _true in
        IntSet.iter (fun i -> clauses.(i)#affect p) _false;
        IntSet.iter (fun i -> clauses.(i)#affect p) _true;
        unsat_clauses <- IntSet.diff unsat_clauses newly_sat;
        decision_level <- decision_level+1;
        Stack.push (p,reason, newly_sat) choices

    method forget =
      let (pivot,how,satisfied) = Stack.pop choices in
      Message.print Message.Debug (lazy("DPLL, forgetting: "^(string_of_int pivot)));
      assert (Global.is_off_assert() || assignment.(index_of_literal pivot) = (value_of_literal pivot));
      assignment.(index_of_literal pivot) <- lUnk;
      let (pos,neg) = prop_to_clauses.(index_of_literal pivot) in
        IntSet.iter (fun i -> clauses.(i)#forget pivot) pos;
        IntSet.iter (fun i -> clauses.(i)#forget pivot) neg;
        unsat_clauses <- IntSet.union unsat_clauses satisfied;
        decision_level <- decision_level-1;
        (pivot,how)

    (** Is there a contradiction (clause impossible to satisfy) ? *)
    method has_contra =
      IntSet.exists (fun i -> clauses.(i)#contradiction) unsat_clauses

    (** Does the current assignment satisfy the system ? *)
    method is_sat = IntSet.is_empty unsat_clauses

    (** Get one of the clause with contradiction (for backtracking)*)
    method private get_unsat_clause =
      let index = find_in_IntSet (fun i -> clauses.(i)#contradiction) unsat_clauses in
        clauses.(index)

    (* Variable choice heuristics *)

    (* Jeroslow-Wang heuristic*)
    method jeroslow_wang =
      let power_of_2 = Array.map (fun cl -> 0.0) clauses in
        IntSet.iter (fun i -> power_of_2.(i) <- exp (-.(float_of_int clauses.(i)#size))) unsat_clauses;
        let max = ref 0.0 in
        let prop = ref None in
          for index = 1 to (Array.length prop_to_clauses) -1 do
            if assignment.(index) = lUnk then
              begin
                let (pos,neg) = prop_to_clauses.(index) in
                let sum = ref 0.0 in
                  IntSet.iter (fun i -> sum := !sum +. power_of_2.(i)) pos;
                  IntSet.iter (fun i -> sum := !sum +. power_of_2.(i)) neg;
                  if !sum > !max then
                    begin
                      max := !sum;
                      let sign = ref 0 in
                        IntSet.iter (fun i -> if not clauses.(i)#is_sat then sign := !sign + 1) pos;
                        IntSet.iter (fun i -> if not clauses.(i)#is_sat then sign := !sign - 1) neg;
                        if !sign >= 0 then prop := Some index
                        else prop := Some (lNot index)
                    end
              end
          done;
          !prop

    (** Returns a variable that satisfies the maximum #clauses.
     * Dynamic Largest Individual Sum (DLIS)
     *)
    method find_max_degree =
      let max = ref 0 in
      let prop = ref None in
        for index = 1 to (Array.length prop_to_clauses) -1 do
          if assignment.(index) = lUnk then
            begin
              let (pos,neg) = prop_to_clauses.(index) in
              let res = ref 0 in
                IntSet.iter (fun i -> if not clauses.(i)#is_sat then res := !res + 1) pos;
                IntSet.iter (fun i -> if not clauses.(i)#is_sat then res := !res - 1) neg;
                if abs !res > !max then
                  begin
                    max := abs !res;
                    if !res > 0  then prop := Some index
                    else prop := Some (lNot index)
                  end
            end
        done;
        !prop

    (** Returns a variable that only satisfies clauses *)
    method find_max_unipolar_variable =
      let max = ref 0 in
      let prop = ref None in
        for pr = 1 to (Array.length prop_to_clauses) -1 do
          if assignment.(pr) = lUnk then
            begin
              let (pos,neg) = prop_to_clauses.(pr) in
              let size_p = IntSet.fold (fun i counter -> if not clauses.(i)#is_sat then counter + 1 else counter) pos 0 in
              let size_n = IntSet.fold (fun i counter -> if not clauses.(i)#is_sat then counter + 1 else counter) neg 0 in
                match (size_p > 0,size_n > 0) with
                | (true,false) -> if size_p > !max then (prop := Some pr; max := size_p)
                | (false,true) -> if size_n > !max then (prop := Some pr; max := size_n)
                | _ -> ()
            end
        done;
        !prop

    (** try to find a clause with only one literal left.
     * @return Some(literal,clause)
     *)
    method find_unit_propagation =
      try 
        let p = find_in_IntSet (fun i -> clauses.(i)#size = 1) unsat_clauses in
        let c = clauses.(p)#get_choice in
          Message.print Message.Debug (lazy("DPLL, unit propagation in "^(string_of_int p)^" with lit "^(string_of_int c)));
          (*Message.print Message.Debug (lazy("DPLL, clause "^(string_of_int p)^" : "^(clauses.(p)#to_string_detailed)));*)
          Some (c,clauses.(p))
      with Not_found -> None

    (** Returns a literal that will make a clause sat*)
    method find_random =
      try Some clauses.(IntSet.choose unsat_clauses)#get_choice
      with Not_found -> None

    (*TODO T-propagation*)
    method decision_policy =
      Message.print Message.Debug (lazy("DPLL, decision_policy: try unit"));
      match self#find_unit_propagation with
      | Some (lit,cl) ->
        begin
          let proof = self#proof_for_clause cl in
            self#affect (lit) (Implied proof)
        end
      | None ->
        begin
          Message.print Message.Debug (lazy("DPLL, decision_policy: try unipolar"));
          match self#find_max_unipolar_variable with
          | Some lit  -> self#affect lit Open
          | None ->
            begin
              Message.print Message.Debug (lazy("DPLL, decision_policy: Jeroslow-Wang"));
              match self#jeroslow_wang with
              | Some lit  -> self#affect lit Open
              | None ->
                begin
                  Message.print Message.Debug (lazy("DPLL, decision_policy: try max degree"));
                  match self#find_max_degree with
                  | Some lit  -> self#affect lit Open
                  | None ->
                    begin
                      Message.print Message.Debug (lazy("DPLL, decision_policy: try random"));
                      match self#find_random with
                      | Some lit  -> self#affect lit Open
                      | None -> failwith "DPLL, decision_policy: no possible affectation"
                    end
                end
            end
        end

    (** to call when unsat + need a proof.
     * (as the learning last clause of not mandatory -> backjump has to make the first affect)
     *)
    method private backjump explanation =
      Message.print Message.Debug (lazy("DPLL, backtracking with: "^(explanation#to_string)));
      let rec build_proof prf =
        try 
          let (pivot, how) = self#forget in
            match how with
            | Open ->
              if (int_get_result prf)#has_prop pivot then
                self#force_learning (int_get_result prf) prf
              else
                build_proof prf
            | Implied proof ->
              if (int_get_result prf)#has_prop pivot then
                begin
                  let resolved_clause = (int_get_result prf)#resolve pivot (int_get_result proof) in
                  (*
                  (* TODO there is some redundant computation somewhere -> improve learning *)
                  let rec ancestor_contains cls prf = match prf with
                    | IRPNode (_, left, right, cls2) ->
                         IntSet.equal cls#get_literals cls2#get_literals
                      || ancestor_contains cls left
                      || ancestor_contains cls right
                    | IRPLeaf cls2 -> IntSet.equal cls#get_literals cls2#get_literals
                  in
                  assert (not (ancestor_contains resolved_clause prf));
                  assert (not (ancestor_contains resolved_clause proof));
                  *)
                  let new_prf =
                    if keep_proof then IRPNode (index_of_literal pivot, prf, proof, resolved_clause)
                    else IRPLeaf resolved_clause
                  in
                    self#choose_to_learn_clause resolved_clause new_prf;
                    build_proof new_prf
                end
              else
                build_proof prf
            | TImplied proof -> (*continue proof further*)
              failwith "DpllCore, backjump: theory deduction not supported for the moment."
        with Stack.Empty ->
          begin (*now we have a proof of unsat*)
            assert (Global.is_off_assert() || (int_get_result prf)#size = 0);
            resolution_proof <- Some prf;
            possibly_sat <- false
          end
      in
        build_proof (self#proof_for_clause explanation)

    method solve =
      if possibly_sat then
        begin
        Message.print Message.Debug (lazy("DPLL, system is possibly sat."));
          if self#is_sat then Some(self#get_assign)
          else if self#has_contra then
            begin
              let cl = self#get_unsat_clause in
                self#backjump cl;
                self#solve
            end
          else
            begin
              self#decision_policy;
              self#solve
            end
        end
      else
        None

    method get_proof_of_unsat =
      match resolution_proof with
      | Some prf -> prf
      | None -> failwith "DPLL, no resolution proof"

    method take i =
      assert (Global.is_off_assert() || i <= decision_level);
      let s = Stack.copy choices in
      let rec take i acc =
        if i = 0 then acc
        else
          begin
            let (pivot,_,_) = Stack.pop s in
              take (i - 1) (pivot :: acc)
          end
      in
        take i []

    method unit_propagate_and_backjump =
      let old_decision_level = decision_level in
      let rec process () = 
        if possibly_sat then
          begin
            Message.print Message.Debug (lazy("DPLL, system is possibly sat."));
            if self#is_sat then
              begin
                let new_decision_level = decision_level in
                  assert(new_decision_level >= old_decision_level);
                  IAffectation (self#take (new_decision_level - old_decision_level), self#get_assign)
              end
            else if self#has_contra then
              begin
                let cl = self#get_unsat_clause in
                  Message.print Message.Debug (lazy("DPLL, backtracking with: "^(cl#to_string)));
                  self#backjump cl;
                  let new_decision_level = decision_level in
                    if new_decision_level < old_decision_level
                    then IBacktracked (old_decision_level - new_decision_level)
                    else process ()
              end
            else
              begin
                match self#find_unit_propagation with
                | Some (lit,cl) ->
                  begin
                    let proof = self#proof_for_clause cl in
                      self#affect (lit) (Implied proof);
                      process ()
                  end
                | None ->
                  begin
                    let new_decision_level = decision_level in
                      assert(new_decision_level >= old_decision_level);
                      IAffected (self#take (new_decision_level - old_decision_level))
                  end
              end
          end
        else
          IProof resolution_proof
      in
        process ()
      

    method next =
      match self#unit_propagate_and_backjump with
      | IAffected [] ->
        begin
          Message.print Message.Debug (lazy("DPLL taking decision_policy branch"));
          self#decision_policy;
          let (pivot,_,_) = Stack.top choices in
            IAffected [pivot] (*TODO better -> unit propagation again ... *)
        end
      | rest -> rest
  end

(*** Wrapper ***)

(* for partial solving *)
type status = Affected of predicate list
            | Affectation of predicate list * predicate list (* newly affected + full affectation that satifies the system *)
            | Backtracked of int (*how many atoms where set to Unk*)
            | Proof of res_proof option (* unsat: return resolution proof if asked *)

class csi_dpll =
  fun with_proof ->
  object (self)

    inherit sat_solver with_proof

    val sys = new system with_proof

    val mutable counter = 0
    method private get_fresh_index = counter <- counter + 1; counter
    val index_to_atom = Hashtbl.create 500
    val atom_to_index = Hashtbl.create 500

    method private get_index atom =
      let proposition = proposition_of_lit atom in
      let index =
        if Hashtbl.mem atom_to_index proposition then
          begin
            Hashtbl.find atom_to_index proposition
          end
        else
          begin
            let index = self#get_fresh_index in
              Hashtbl.add atom_to_index proposition index;
              Hashtbl.add index_to_atom index proposition;
              index
          end
      in
        if atom = proposition then index else -index

    method private get_atom index =
      let at = Hashtbl.find index_to_atom (abs index) in
        if (value_of_literal index) = lFalse then
          normalize_only (Not at)
        else
          at
    
    method private convert_clause formula = match formula with
      | Or lst -> List.map (fun x -> (self#get_index x)) lst;
      | err -> failwith ("DpllCore, convert_clause: expecting disjunction, given: "^ print err)

    method init formulae =
      match formulae with
      | And lst ->
        begin
          assert(Global.is_off_assert() || counter = 0);(* i.e. first time it is initialized *)
          let converted = List.map (fun x -> self#convert_clause x) lst in
            sys#resize counter;
            sys#init converted
        end
      | err -> failwith ("DpllCore, init: expecting CNF, given: "^ print err)
    
    method add_clause formula =
      Message.print Message.Debug (lazy("DPLL, adding "^(print_pred formula)));
      let old_index = counter in
      let lst = self#convert_clause formula in
        if old_index < counter then sys#resize counter;
        sys#add_clause lst
    
    val mutable last_solution: predicate list option = None
    method solve = match sys#solve with
      | Some sol -> last_solution <- Some (List.map self#get_atom sol); true
      | None -> last_solution <- None; false

    method get_solution = match last_solution with
      | Some sol -> sol
      | None -> failwith "DpllCore: no solution for the moment"
    
    method get_proof =
      let partial_translation = Hashtbl.create 1000 in
      let transform_clause cl =
        let lits = cl#get_literals in
          IntSet.fold
            (fun i acc -> PredSet.add (self#get_atom i) acc)
            lits PredSet.empty
      in
      let rec transform proof =
        let cl = int_get_result proof in
          if Hashtbl.mem partial_translation cl then
            Hashtbl.find partial_translation cl
          else
            begin
              match proof with
              | IRPLeaf cl ->
                begin
                  let translation = RPLeaf (transform_clause cl) in
                    Hashtbl.add partial_translation cl translation;
                    translation
                end
              | IRPNode (pivot, left, right, cl) ->
                begin
                  let transformed_pivot  = self#get_atom pivot in
                  let transformed_left   = transform left in
                  let transformed_right  = transform right in
                  let transformed_clause = transform_clause cl in
                  let translation = RPNode (transformed_pivot, transformed_left, transformed_right, transformed_clause) in
                    Hashtbl.add partial_translation cl translation;
                    translation
                end
            end
      in
      let proof = sys#get_proof_of_unsat in 
      let transformed = transform proof in
        (* output the satsolver proof *)
        (*Message.print Message.Debug (lazy(string_of_proof transformed));*)
        Message.print Message.Debug (lazy(tracecheck_of_proof transformed));
        transformed


    method next =
      let atoms = List.map self#get_atom in
        match sys#next with
        | IAffected lst -> Affected (atoms lst)
        | IAffectation (lst1, lst2) -> Affectation (atoms lst1, atoms lst2)
        | IBacktracked level -> Backtracked level
        | IProof prf ->
          begin
            match prf with
            | Some _ -> Proof (Some self#get_proof)
            | None -> Proof None
          end

    method is_consistent = not sys#has_contra
    method is_sat = sys#is_sat
    method pop = ignore(sys#forget)
    method get_decision_level = sys#get_decision_level

  end

