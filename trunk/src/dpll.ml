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

(*a very simple dpll SAT solver*)
(*TODO improve*)

let contra x = AstUtil.normalize_only (Not x)

class clause =
  fun disj l ->
  object (self)
    val propositions = match disj with
      | Or lst -> List.fold_left (fun acc x -> AstUtil.PredSet.add x acc) AstUtil.PredSet.empty lst
      | _ -> "DPLL: clause expect a disjunction"
    
    val learned = l
    val mutable left = propositions
    val mutable satisfied = AstUtil.PredSet.empty

    method has el = AstUtil.PredSet.mem el propositions
    method has_not el = AstUtil.PredSet.mem (contra el) propositions

    method props = (*proposition in clause*)
      AstUtil.PredSet.fold
        (fun e acc -> let p = AstUtil.get_proposition e in AstUtil.PredSet.add p acc)
        propositions AstUtil.PredSet.empty
    method pos_props = AstUtil.PredSet.filter self#has     self#props
    method neg_props = AstUtil.PredSet.filter self#has_not self#props

    method get_choices = left
    method get_choice = AstUtil.PredSet.chosse left
    method is_sat = not (AstUtil.PredSet.is_empty satisfied)
    method contradiction = AstUtil.PredSet.is_empty left

    method size = AstUtil.PredSet.cardinal left

    method affect atom =
      let contr = contra atom in
      if AstUtil.PredSet.mem atom propositions then
        satisfied <- AstUtil.PredSet.add atom satisfied;
      if AstUtil.PredSet.mem contr propositions then
        left <- AstUtil.PredSet.remove contr left

    method forget atom =
      let contr = contra atom in
      if AstUtil.PredSet.mem atom propositions then
        satisfied <- AstUtil.PredSet.remove atom satisfied;
      if AstUtil.PredSet.mem contr propositions then
        left <- AstUtil.PredSet.add contr left
    
  end

let compare_clauses a b = a#size - b#size

type var_assign = Open | Closed | Implied

class sytem =
  object (self)
    
    
    val mutable clauses = Array.make 0 (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true )
    val mutable props = []
    val mutable affected = AstUtil.PredSet.empty
    val choices = Stack.create ()
    val prop_to_clauses = Hashtbl.create 123


    method reset =
      clauses <- Array.make 0 (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true);
      props <- [];
      affected <- AstUtil.PredSet.empty;
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
      props <- AstUtil.get_proposition formula;
      List.iter (fun x -> Hashtbl.add prop_to_clauses x ([],[])) props;
      match formula with
      | And lst ->
        begin
          let n = List.length lst in
            clauses <- Array.make n (new clause (Or [Eq(Constant 1.0,Constant 1.0)]) true);
            List.fold_left (fun i e -> 
                let cl = new clause e false in
                  clauses.(i) <- cl;
                  let pos = cl#pos_props in AstUtil.PredSet.iter (fun x -> self#add_pos_clause_for_prop x cl) pos;
                  let neg = cl#neg_props in AstUtil.PredSet.iter (fun x -> self#add_neg_clause_for_prop x cl) neg;
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
          i := i+1
        done;
        !c

    method is_sat =
      let i = ref 0 in
      let n = Array.length clauses in
      let s = ref true in
        while !s && !i < n do
          s := clauses.(!i)#is_sat;
          i := i+1
        done;
        !s

    method affect p =
      assert (not (AstUtil.PredSet.mem (contra p) affected));
      affected <- AstUtil.PredSet.add p affected;
      Array.iter (fun x -> x#affect p) clauses

    method forget p =
      assert (AstUtil.PredSet.mem p affected);
      affected <- AstUtil.PredSet.remove p affected;
      Array.iter (fun x -> x#forget p) clauses

    (*return the first clause that satisfies fct*)
    method scan_clauses fct =
      let i = ref 0 in
      let n = Array.length clauses in
      let ans = ref false in
        while (not !ans) && !i < n do
          ans := fct clauses.(!i);
          i := i+1
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
            if not (AstUtil.PredSet.mem pr affect) || not (AstUtil.PredSet.mem (contra pr) affect) then
              begin
                let pos = List.filter (fun x -> not x#satisfied) pos in
                let neg = List.filter (fun x -> not x#satisfied) neg in
                  match (pos,neg) with
                  | ([],[]) -> ()
                  | (p, []) -> if List.lenght p > !max then (prop := Some pr; max := List.lenght p)
                  | ([], n) -> if List.lenght n > !max then (prop := Some (contra pr); max := List.lenght n)
                  | _ -> ()
              end
          ) prop_to_clauses;
        !prop

    method find_unit_propagation =
      match self#scan_clauses (fun x -> x#size = 1) with
        Some p -> let c = p#get_choice in Some c
        None -> None

    (*return a variable that satisfies the maximun #clauses *)
    method find_max_degree =
      let max = ref 0 in
      let prop = ref None in
        Hashtbl.iter
          (fun pr (pos,neg) ->
            if not (AstUtil.PredSet.mem pr affect) || not (AstUtil.PredSet.mem (contra pr) affect) then
              begin
                let pos = List.filter (fun x -> not x#satisfied) pos in
                let neg = List.filter (fun x -> not x#satisfied) neg in
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
      let lst = self#filter_clauses (fun x -> not x#satisfied) in
      let length = List.lenght lst in
      let n = Random.int length in
      let c = (List.nth lst n) in
        Some c#get_choice
      

    (*returns the first possible choice to change*)
    (*if raise empty => unsat (no more branch to explore)*)
    method backjump explanation =
      let props = AstUtil.get_proposition explanation in
      let rec to_next_free () =
        match Stack.pop choices with
        | (p, Open) -> p
        | (p,_) -> (forget p; to_next_free ())
      in
      let rec unstack () =
        let (p,status) = Stack.pop choices in
          forget p;
          if OrdSet.mem p props then
            begin
              match status with
              | Open -> p
              | _ -> to_next_free ()
            end
          else
            unstack ()
      in
        unstack ()

      (*TODO pick choice + T-propagation*)
  end
