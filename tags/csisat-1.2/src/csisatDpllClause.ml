(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *  Copyright (C) 2007-2008  The CSIsat team
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
 *  For information about the CSIsat project,
 *  please visit the CSIsat web page at:
 *  http://www.cs.sfu.ca/~dbeyer/CSIsat/

 *)

(** Part of the DPLL: Clause *)

open   CsisatAst
open   CsisatAstUtil
(**/**)
module Utils   = CsisatUtils
(**/**)

(** Clause: (disjunction of literals) for the sat solver.
 *  Literals are stored in sets (log lookup/insert/del).
 *)
class clause =
  fun disj (l:bool) ->
  object (self)
    val propositions = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    method get_propositions = propositions (*oups, means literals*)

    (*OrdSet*)
    method literals = 
      let lst = PredSet.fold (fun e acc -> e::acc) propositions [] in
        OrdSet.list_to_ordSet lst
    
    (** a learned clause comes from the backtracking*)
    val learned = l
    method is_learned = learned

    val mutable left = match disj with
      | Or lst -> List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty lst
      | _ -> failwith "DPLL: clause expect a disjunction"
    val mutable satisfied = PredSet.empty

    (** has litteral ?*)
    method has el = PredSet.mem el propositions
    (** has (Not litteral) ?*)
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

    (** decision for a variable*)
    method affect atom =
      let contr = contra atom in
      if PredSet.mem atom propositions then
        begin
          satisfied <- PredSet.add atom satisfied;
          left <- PredSet.remove atom left
        end;
      if PredSet.mem contr propositions then
        left <- PredSet.remove contr left

    (** unassign a variable (during backtracking) *)
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

    (* Exists x. x and ¬x in clause*)
    method has_el_and_contra =
      PredSet.exists (fun x -> PredSet.mem (contra x) propositions) propositions
    
    method to_string =
      (Utils.string_list_cat ", "
        (PredSet.fold (fun x acc -> (print x)::acc) propositions []))

    method to_string_dimacs atom_to_int =
      (Utils.string_list_cat " "
        (PredSet.fold
          (fun x acc -> (string_of_int (atom_to_int x))::acc)
          propositions ["0"]))
    
    method to_string_detailed =
      "clause: " ^
      (Utils.string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) propositions [])) ^ "\n" ^
      "satisfied is: " ^
      (Utils.string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) satisfied [])) ^ "\n" ^
      "left is: " ^
      (Utils.string_list_cat ", " (PredSet.fold (fun x acc -> (print x)::acc) left [])) ^ "\n"
  end
