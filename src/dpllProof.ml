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

(** Part of the DPLL: (resolution) Proof *)

open Ast
open AstUtil
open DpllClause

(** Resolution proof*)
type res_proof = RPNode of predicate * res_proof * res_proof * clause (** pivot, left, right, result*)
               | RPLeaf of clause (** A leaf is simply a clause.*)


let get_result proof = match proof with
  | RPNode (_,_,_,r) -> r
  | RPLeaf r -> r

let string_of_proof prf =
  let buffer = Buffer.create 1024 in
  let fill_offset offset = 
    for i = 1 to offset do
      Buffer.add_char buffer ' '
    done;
  in
  let rec print_prf prf offset =
    match prf with
    | RPLeaf cl ->
      begin
        fill_offset offset;
        Buffer.add_string buffer "Leaf node: ";
        Buffer.add_string buffer (cl#to_string);
        Buffer.add_char buffer '\n'
      end
    | RPNode (pivot,left,right,new_cl) ->
      begin
        fill_offset offset;
        Buffer.add_string buffer ("Inner node with pivot "^(print pivot)^": ");
        Buffer.add_string buffer (new_cl#to_string);
        Buffer.add_char buffer '\n';
        print_prf left (offset + 4);
        print_prf right (offset + 4)
      end
  in
    print_prf prf 0;
    Buffer.contents buffer

let tracecheck_of_proof prf =
  let counter = ref 0 in
  let get_fresh_index () = counter := !counter + 1; !counter in
  let index_to_atom = Hashtbl.create 500 in
  let atom_to_index = Hashtbl.create 500 in
  let get_index_atom atom =
    assert(is_atomic atom);
    let proposition = List.hd (get_proposition atom) in
    let index =
      if Hashtbl.mem atom_to_index proposition then
        begin
          Hashtbl.find atom_to_index proposition
        end
      else
        begin
          let index = get_fresh_index () in
            Hashtbl.add atom_to_index proposition index;
            Hashtbl.add index_to_atom index proposition;
            index
        end
    in
      if atom = proposition then index else -index
  in
  let buffer = Buffer.create 10000 in
  let indexes = Hashtbl.create 1000 in
  let counter = ref 1 in
  let get_index cl =
    try Hashtbl.find indexes cl
    with Not_found ->
      begin
        let index = !counter in
          counter := !counter+1;
          Hashtbl.add indexes cl index;
          index
      end
  in
  let printed = Hashtbl.create 1000 in
  let is_printed x =
    try Hashtbl.find printed x
    with Not_found -> false
  in
  let rec print_prf prf =
    if not (is_printed (get_result prf)) then
      begin
        Hashtbl.add printed (get_result prf) true;
        match prf with
        | RPLeaf cl ->
          begin
            Buffer.add_string buffer (string_of_int (get_index cl));
            Buffer.add_char buffer ' ';
            Buffer.add_string buffer (cl#to_string_dimacs get_index_atom);
            Buffer.add_string buffer " 0\n"
          end
        | RPNode (pivot,left,right,new_cl) ->
          begin
            print_prf left;
            print_prf right;
            Buffer.add_string buffer (string_of_int (get_index new_cl));
            Buffer.add_char buffer ' ';
            Buffer.add_string buffer (new_cl#to_string_dimacs get_index_atom);
            Buffer.add_char buffer ' ';
            Buffer.add_string buffer (string_of_int (get_index (get_result left)));
            Buffer.add_char buffer ' ';
            Buffer.add_string buffer (string_of_int (get_index (get_result right)));
            Buffer.add_string buffer " 0\n"
          end
      end
  in
    print_prf prf;
    Buffer.contents buffer

let print_solution lst =
  (*TODO numerical order*)
  let str_lst = (List.fold_left
          (fun acc x -> match x with
            | Atom i -> (" "^(string_of_int i))::acc
            | Not(Atom i) -> (" "^(string_of_int (-i)))::acc
            | _ -> failwith "not an atom")
          [] lst)
  in
  let buffer = Buffer.create 1000 in
    Buffer.add_string buffer "v";
    let rec print_lit lst counter = match lst with
      | x::xs ->
        begin
          let n = (String.length x) + counter in
            Buffer.add_string buffer x;
            if n > 78 then
              begin
                Buffer.add_string buffer "\nv";
                print_lit xs 1
              end
            else
              print_lit xs n
        end
      | [] -> Buffer.add_string buffer " 0";
    in
      print_lit str_lst 1;
      Buffer.contents buffer


