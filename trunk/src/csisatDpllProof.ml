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

(** Part of the DPLL: (resolution) Proof *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatDpllClause

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
