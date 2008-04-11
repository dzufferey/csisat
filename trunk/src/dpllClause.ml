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

class clause =
  fun disj (l:bool) ->
  object (self)
    val propositions = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    method get_propositions = propositions (*oups, means literals*)
    
    val learned = l
    method is_learned = learned

    val mutable left = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    val mutable satisfied = PredSet.empty

    method has el = PredSet.mem el propositions
    method has_not el = PredSet.mem (contra el) propositions

    method props = (*proposition in clause not literal*)
      PredSet.fold
        (fun e acc -> let p = List.hd (get_proposition e) in PredSet.add p acc)
        propositions PredSet.empty
    method pos_props = PredSet.filter self#has     self#props
    method neg_props = PredSet.filter self#has_not self#props

    method get_choices = left
    method get_choice = PredSet.choose left
    method is_sat = not (PredSet.is_empty satisfied)
    method contradiction = (not self#is_sat) && PredSet.is_empty left

    method size = PredSet.cardinal left

    method affect atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        begin
          satisfied <- PredSet.add atom satisfied;
          left <- PredSet.remove atom left
        end;
      if PredSet.mem contr propositions then
        left <- PredSet.remove contr left

    method forget atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        begin
          satisfied <- PredSet.remove atom satisfied;
          left <- PredSet.add atom left
        end;
      if PredSet.mem contr propositions then
        left <- PredSet.add contr left

    method get_satisfied = satisfied

    method has_el_and_contra =
      PredSet.exists (fun x -> PredSet.mem (contra x) propositions) propositions
    
    method to_string =
      (Utils.string_list_cat ", "
        (PredSet.fold (fun x acc -> (print x)::acc) propositions []))

    method to_string_dimacs =
      (Utils.string_list_cat " "
        (PredSet.fold
          (fun x acc -> match x with
            | Atom i -> (string_of_int i)::acc
            | Not(Atom i) -> (string_of_int (-i))::acc
            | _ -> failwith "not an atom")
          propositions ["0"]))
    
    method to_string_detailed =
      "clause: " ^
      (Utils.string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) propositions [])) ^ "\n" ^
      "satisfied is: " ^
      (Utils.string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) satisfied [])) ^ "\n" ^
      "left is: " ^
      (Utils.string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) left [])) ^ "\n"
  end
