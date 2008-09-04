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

(** Interface for PicoSat.
 * As PicoSat is stateful it is not possible to have more than one solver at the time. 
 *)

open   CsisatAst
open   CsisatAstUtil
open   CsisatSatInterface
open   CsisatDpllClause
open   CsisatDpllProof
(**/**)
module Message = CsisatMessage
(**/**)

let initialized = ref false;

class picosat with_proof =
  object (self)
    inherit sat_solver with_proof

    initializer
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
    method private get_atom index =
      let at = Hashtbl.find index_to_atom (abs index) in
        if index < 0 then
          normalize_only (Not at)
        else
          at

    method init formulae = match formulae with
      | And lst -> List.iter (fun x -> self#add_clause x) lst
      | err -> failwith ("PicoInterface, init: expecting CNF, given: "^ print err)
    
    method add_clause formula = match formula with
      | Or lst ->
        begin
          List.iter (fun x -> Camlpico.add (self#get_index x)) lst;
          Camlpico.add 0
        end
      | err -> failwith ("PicoInterface, add_clause: expecting disjunction, given: "^ print err)

    method solve = 
      let res = Camlpico.sat (-1) in
        if (res = Camlpico.satisfiable()) then true
        else if (res = Camlpico.unsatisfiable()) then false
        else if (res = Camlpico.unknown()) then failwith "satPL: PicoSat said UNKNOWN"
        else failwith "satPL: does not understand what PicoSat said"

    method get_solution = 
      let max_lit = counter in
      let a = Array.make (max_lit + 1) (Atom (Internal 0), 0) in
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
        
    method get_proof =
      let idx_to_clause = Hashtbl.create 1000 in
      let raw = Camlpico.get_proof () in
      let (_,_,_,seps) = Array.fold_left
        (fun (start, current, nb0, seps) x ->
          if x = 0 then
            begin
              if nb0 >= 1 then
                (current + 1, current + 1, 0, (start,current - start + 1)::seps)
              else (start, current + 1, nb0 + 1, seps) 
            end
          else (start, current + 1, nb0, seps) 
        ) (0,0,0,[]) raw
      in
      (* structure the zhains*)
      let zhains = List.rev_map 
        (fun (start,len) ->
          let raw_zhain = Array.sub raw start len in
          let idx = raw_zhain.(0) in
          let lits = ref [] in
          let parents = ref [] in
          let i = ref 1 in
            while raw_zhain.(!i) <> 0 do
              assert (!i < Array.length raw_zhain);
              lits := (raw_zhain.(!i)) :: !lits;
              i := !i + 1
            done;
            i := !i + 1;
            while raw_zhain.(!i) <> 0 do
              assert (!i < Array.length raw_zhain);
              parents := (raw_zhain.(!i)) :: !parents;
              i := !i + 1
            done;
            assert(!i = ((Array.length raw_zhain) -1));
            (*buils the clauses*)
            let atoms = List.map self#get_atom !lits in
            let cl = List.fold_left (fun acc x -> PredSet.add x acc) PredSet.empty atoms in
              Hashtbl.add idx_to_clause idx cl;
              (idx, cl, !parents)
        ) seps
      in
        Message.print Message.Debug (lazy("#zhains "^(string_of_int (List.length zhains))));
        (*build the proof*)
        let proof_cache = Hashtbl.create 1000 in
        List.iter
          (fun (id, clause, parents) ->
            Message.print Message.Debug (lazy("building proof for zhain "^(string_of_int id)));
            (*assume the proof is "in order"*)
            if (List.length parents) = 0 then
              begin
                Hashtbl.add proof_cache id (RPLeaf clause)
              end
            else
              begin
                assert ((List.length parents) > 1);
                let prf = List.fold_left
                  (fun left id ->
                    Message.print Message.Debug (lazy("searching "^(string_of_int id)));
                    let right = Hashtbl.find proof_cache id in
                    let left_lit = get_result left in
                    let right_lit = get_result right  in
                    let neg_right_lit = PredSet.fold
                      (fun x acc -> PredSet.add (contra x) acc)
                      right_lit PredSet.empty
                    in
                    let pivot_set = PredSet.inter left_lit neg_right_lit in
                      assert((PredSet.cardinal pivot_set) = 1);
                      (*TODO the order of the parents is arbitrary*)
                    let pivot = proposition_of_lit (PredSet.choose pivot_set) in
                      let new_lits =
                        PredSet.remove (contra pivot)
                         (PredSet.remove pivot
                           (PredSet.union left_lit right_lit))
                      in
                        RPNode(pivot, left, right, new_lits)
                  )
                  (Hashtbl.find proof_cache (List.hd parents)) (List.tl parents)
                in
                  Hashtbl.add proof_cache id prf
              end
          ) zhains;
          let (last,_,_) = List.hd (List.rev zhains) in
            Message.print Message.Debug (lazy("searching "^(string_of_int last)));
            Hashtbl.find proof_cache last

  end
