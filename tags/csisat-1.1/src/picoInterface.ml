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
open DpllClause
open DpllProof

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
          AstUtil.normalize_only (Not at)
        else
          at

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
            let cl = new clause (Or atoms) false in
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
                    let cll = get_result left in
                    let clr = get_result right in
                    let left_lit = cll#get_propositions in
                    let right_lit = clr#get_propositions in
                    let neg_right_lit = AstUtil.PredSet.fold
                      (fun x acc -> AstUtil.PredSet.add (AstUtil.contra x) acc)
                      right_lit AstUtil.PredSet.empty
                    in
                    let pivot_set = AstUtil.PredSet.inter left_lit neg_right_lit in
                      assert((AstUtil.PredSet.cardinal pivot_set) = 1);
                      (*TODO the order of the parents is arbitrary*)
                    let pivot = AstUtil.proposition_of_lit (AstUtil.PredSet.choose pivot_set) in
                      let new_lits =
                        AstUtil.PredSet.fold (fun x acc -> x::acc)
                          (AstUtil.PredSet.remove (AstUtil.contra pivot)
                            (AstUtil.PredSet.remove pivot
                              (AstUtil.PredSet.union left_lit right_lit))) []
                      in
                      let new_cl = new clause (Or new_lits) false in
                        RPNode(pivot, left, right, new_cl)
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
