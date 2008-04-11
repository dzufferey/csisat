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
open SatInterface

let initialized = ref false;

class picosat with_proof =
  object (self)
    inherit sat_solver with_proof

    initializer
      assert (not with_proof); (*TODO*)
      if !initialized then Camlpico.reset ();
      Camlpico.init ();
      initialized := true;
      if with_proof then Camlpico.enable_trace ()

    val mutable counter = 0
    method private get_fresh_index = counter <- counter + 1; counter
    val index_to_atom = Hashtbl.create 500
    val atom_to_index = Hashtbl.create 500
    method private get_index atom =
      assert(is_atomic atom);
      let proposition = List.hd (get_proposition atom) in
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

    method init formulae = match formulae with
      | And lst -> List.iter (fun x -> self#add_clause x) lst
      | err -> failwith ("PicoInterface, init: expecting CNF, given: "^AstUtil.print err)
    
    method add_clause formula = match formula with
      | Or lst ->
        begin
          List.iter (fun x -> Camlpico.add (self#get_index x)) lst;
          Camlpico.add 0
        end
      | err -> failwith ("PicoInterface, add_clause: expecting disjunction, given: "^AstUtil.print err)

    method solve = 
      let res = Camlpico.sat (-1) in
        if (res = Camlpico.satisfiable()) then true
        else if (res = Camlpico.unsatisfiable()) then false
        else if (res = Camlpico.unknown()) then failwith "satPL: PicoSat said UNKNOWN"
        else failwith "satPL: does not understand what PicoSat said"

    method get_solution = 
      let max_lit = counter in
      let a = Array.make (max_lit + 1) (Atom 0, 0) in
        for i = 1 to max_lit do
          a.(i) <- (Hashtbl.find index_to_atom i, Camlpico.deref i)
        done;
        let lst = Utils.map_filter
          (fun (a,i) ->
            if i = 1 then Some (a, true)
            else if i = -1 then Some (a, false)
            else if i = 0 then None
            else failwith ("SatPL, get_sat_assign: picosat told "^(string_of_int i))
          )
          (Array.to_list a)
        in
          List.map (fun (atom, value) -> if value then atom else normalize_only (Not atom)) lst
        
    method get_proof = failwith "Pico: not proof support for the moment, sorry"
  end
