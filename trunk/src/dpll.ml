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
open AstUtil

(*a very simple dpll SAT solver*)
(*TODO improve*)


class clause =
  fun disj l ->
  object (self)
    val propositions = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    method get_propositions = propositions
    
    val learned = l
    val mutable left = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    val mutable satisfied = PredSet.empty

    method has el = PredSet.mem el propositions
    method has_not el = PredSet.mem (contra el) propositions

    method props = (*proposition in clause*)
      PredSet.fold
        (fun e acc -> let p = List.hd (get_proposition e) in PredSet.add p acc)
        propositions PredSet.empty
    method pos_props = PredSet.filter self#has     self#props
    method neg_props = PredSet.filter self#has_not self#props

    method get_choices = left
    method get_choice = PredSet.choose left
    method is_sat = not (PredSet.is_empty satisfied)
    method contradiction = PredSet.is_empty left

    method size = PredSet.cardinal left

    method affect atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        satisfied <- PredSet.add atom satisfied;
      if PredSet.mem contr propositions then
        left <- PredSet.remove contr left

    method forget atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        satisfied <- PredSet.remove atom satisfied;
      if PredSet.mem contr propositions then
        left <- PredSet.add contr left
    
  end

let compare_clauses a b = a#size - b#size

type var_assign = Open | Closed | Implied | TImplied
(*a resolution proof*)
type res_proof = RPNode of predicate * res_proof * res_proof * PredSet.t (*pivot left right result*)
               | RPLeaf of PredSet.t
let get_result proof = match proof with
  | RPNode (_,_,_,r) -> r
  | RPLeaf r -> r

class sytem =
  fun with_prf ->
  object (self)
    
    
    val mutable clauses = Array.make 0 (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true )
    val mutable props = PredSet.empty
    val mutable affected = PredSet.empty
    val choices = Stack.create ()
    val prop_to_clauses = Hashtbl.create 123
    val keep_proof = with_prf

    method reset =
      clauses <- Array.make 0 (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true);
      props <- PredSet.empty;
      affected <- PredSet.empty;
      Hashtbl.clear prop_to_clauses;
      Stack.clear choices

    method add_pos_clause_for_prop p cl =
      let (oldp, oldn) = try Hashtbl.find prop_to_clauses p with Not_found -> ([],[]) in
        Hashtbl.replace prop_to_clauses p (cl::oldp, oldn)
    method add_neg_clause_for_prop p cl =
      let (oldp, oldn) = try Hashtbl.find prop_to_clauses p with Not_found -> ([],[]) in
        Hashtbl.replace prop_to_clauses p (oldp, cl::oldn)

    
    (*assume CNF*)
    method init formula = 
      props <- get_proposition_set formula;
      PredSet.iter (fun x -> Hashtbl.add prop_to_clauses x ([],[])) props;
      match formula with
      | And lst ->
        begin
          let n = List.length lst in
            clauses <- Array.make n (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true);
            List.fold_left (fun i e -> 
                let cl = new clause e false in
                  clauses.(i) <- cl;
                  let pos = cl#pos_props in PredSet.iter (fun x -> self#add_pos_clause_for_prop x cl) pos;
                  let neg = cl#neg_props in PredSet.iter (fun x -> self#add_neg_clause_for_prop x cl) neg;
                    i + 1
              ) 0 lst;
        end
      | _ -> failwith "DPLL: expect CNF"
     
    method has_contra = 
      let i = ref 0 in
      let n = Array.length clauses in
      let c = ref false in
        while (not !c) && !i < n do
          c := clauses.(!i)#contradiction;
          i := !i + 1
        done;
        !c

    method is_sat =
      let i = ref 0 in
      let n = Array.length clauses in
      let s = ref true in
        while !s && !i < n do
          s := clauses.(!i)#is_sat;
          i := !i + 1
        done;
        !s

    method affect p reason =
      assert (not (PredSet.mem (contra p) affected));
      Stack.push (p,reason) choices;
      affected <- PredSet.add p affected;
      Array.iter (fun x -> x#affect p) clauses

    method forget p =
      assert (PredSet.mem p affected);
      affected <- PredSet.remove p affected;
      Array.iter (fun x -> x#forget p) clauses

    method get_assign =
      PredSet.fold (fun a acc -> a::acc) affected []
    
    method get_assigned_props =
      List.flatten (List.map get_proposition self#get_assign)

    (*return the first clause that satisfies fct*)
    method scan_clauses fct =
      let i = ref 0 in
      let n = Array.length clauses in
      let ans = ref false in
        while (not !ans) && !i < n do
          ans := fct clauses.(!i);
          i := !i + 1
        done;
        if !i >= n then None else Some clauses.(!i)
    
    method filter_clauses fct =
      List.filter fct (Array.to_list clauses)

    (*return a variable that only satisfies clauses *)
    method find_max_unipolar_variable =
      let max = ref 0 in
      let prop = ref None in
        Hashtbl.iter
          (fun pr (pos,neg) ->
            if not (PredSet.mem pr affected) || not (PredSet.mem (contra pr) affected) then
              begin
                let pos = List.filter (fun x -> not x#is_sat) pos in
                let neg = List.filter (fun x -> not x#is_sat) neg in
                  match (pos,neg) with
                  | ([],[]) -> ()
                  | (p, []) -> if List.length p > !max then (prop := Some pr; max := List.length p)
                  | ([], n) -> if List.length n > !max then (prop := Some (contra pr); max := List.length n)
                  | _ -> ()
              end
          ) prop_to_clauses;
        !prop

    method find_unit_propagation =
      match self#scan_clauses (fun x -> x#size = 1) with
      | Some p -> let c = p#get_choice in Some c
      | None -> None

    (*return a variable that satisfies the maximun #clauses *)
    method find_max_degree =
      let max = ref 0 in
      let prop = ref None in
        Hashtbl.iter
          (fun pr (pos,neg) ->
            if not (PredSet.mem pr affected) || not (PredSet.mem (contra pr) affected) then
              begin
                let pos = List.filter (fun x -> not x#is_sat) pos in
                let neg = List.filter (fun x -> not x#is_sat) neg in
                  if abs ((List.length pos) - (List.length neg)) > !max then
                    begin
                      max := abs ((List.length pos) - (List.length neg));
                      if (List.length pos) - (List.length neg) > 0
                        then prop := Some pr
                        else prop := Some (contra pr)
                    end
              end
          ) prop_to_clauses;
        !prop
      
    method find_random =
      let lst = self#filter_clauses (fun x -> not x#is_sat) in
      let length = List.length lst in
      let n = Random.int length in
      let c = (List.nth lst n) in
        Some c#get_choice
      

    method get_unsat_clause =
      match self#scan_clauses (fun x -> x#contradiction) with
      | Some cl -> cl
      | None -> failwith "DPLL: get_unsat_clause called without contradiction"

   method get_unit_propagation prop =
     let pos_prop = List.hd (get_proposition prop) in
     let (pos,neg) = Hashtbl.find prop_to_clauses pos_prop in
     let find_clause lst =
       let set = PredSet.singleton prop in
         List.filter (fun x -> x#get_choices = set) lst
     in  
       if pos_prop = prop then
         begin
           let possibility = find_clause pos in
             assert (List.length possibility > 0);
             List.hd possibility
         end
       else
         begin
           let possibility = find_clause neg in
             assert (List.length possibility > 0);
             List.hd possibility
         end

    
    (*returns the first possible choice to change*)
    (*explanation is a clause to satisfy*)
    (*if raise empty => unsat (no more branch to explore)*)
    method backjump explanation =
      let props = explanation#props in
      let rec to_next_free () =
        match Stack.pop choices with
        | (p, Open) -> self#affect p Closed
        | (p,_) -> (self#forget p; to_next_free ())
      in
      let rec unstack () =
        let (p,status) = Stack.pop choices in
          self#forget p;
          if PredSet.mem (contra p) props then
            begin
              match status with
              | Open -> self#affect p Closed
              | _ -> to_next_free ()
            end
          else
            unstack ()
      in
        unstack ()
(*
type res_proof = RPNode of predicate * res_proof * res_proof * PredSet.t (*pivot left right result*)
               | RPLeaf of PredSet.t
*)
    val partial_proofs = Hashtbl.create 1024
    (** to call when unsat + need a proof
     *)
    method resolution_proof explanation =
      let rec build_proof prf =
        try 
          let (pivot, how) = Stack.pop choices in
            self#forget pivot;
            match how with
            | Open -> (*can stop the proof here and pick new assign*)
              begin
                let assigned = OrdSet.list_to_ordSet (self#get_assigned_props) in
                let choices = (PredSet.fold (fun x acc -> x::acc) (get_result prf) []) in
                let choices_props = OrdSet.list_to_ordSet (List.flatten (List.map get_proposition choices)) in
                let resulting = OrdSet.substract choices_props assigned in
                  Message.print Message.Debug (lazy("resulting var choice has length: "^(string_of_int (List.length resulting))));
                  assert (List.length resulting > 0);
                  self#affect (List.hd resulting) Closed;
                  (*TODO save proof*)()
              end
            | Closed -> (*can stop the proof here, but need to backtrack further*)
              begin
                self#backjump explanation;
                (*TODO save proof*)()
              end
            | Implied -> (*continue proof further*)
              begin
                let satisfied_clause = self#get_unit_propagation pivot in
                let props_of_sat = satisfied_clause#props in
                let new_unsat_disj = PredSet.remove (contra pivot) (PredSet.remove pivot (PredSet.union (get_result prf) props_of_sat)) in
                let new_prf = RPNode (pivot, RPLeaf props_of_sat, prf, new_unsat_disj) in
                  build_proof new_prf
              end
            | TImplied -> (*continue proof further*)
              begin
                (*TODO need T-lemma*)
                failwith "DPLL: theory deduction yet to come"
              end
        with Stack.Empty ->
          begin (*now we have a proof of unsat*)
            assert (get_result prf = PredSet.empty);
            (*TODO*) failwith "TODO"
          end
      in
        build_proof (RPLeaf explanation#props)


   method new_clause cl =
     List.iter (cl#affect) self#get_assign;
     clauses <- Array.append clauses (Array.make 1 cl);
     if cl#contradiction then
       begin
         if keep_proof then
           self#backjump cl
         else
           self#resolution_proof cl
       end

   method add_clause disj =
     let cl = new clause disj false in
       self#new_clause cl
   
   method learned_clause disj =
     let cl = new clause disj true in
       self#new_clause cl

    (*TODO pick choice + T-propagation*)
  end
