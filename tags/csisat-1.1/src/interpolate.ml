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

type side_t = A | B | Mixed

let side_to_string s = match s with
  | A -> "A"
  | B -> "B"
  | Mixed -> "Mixed"

let splitN_unsat_cores terms_lst mixed =
  let terms = Array.of_list terms_lst in
  let parts = Array.make (Array.length terms) [] in
  let rec process x =
    Array.iteri
      (fun i term ->
        if OrdSet.mem x term then parts.(i) <- x::(parts.(i));
      ) terms
  in
    List.iter process mixed;
    Array.to_list parts

(* this should be used only when boolean contradicion are not important (i.e. sat solver took care of them)
 * The blocking clauses can intorduce equalities that are not part of A or B
 *)
let splitN_unsat_cores_set proposition_lst mixed =
  let props = Array.of_list proposition_lst in
  let parts = Array.make (Array.length props) [] in
  let rec process x =
    let assigned = ref false in
      (*new lit introduced by blocking clause, put it in the leftmost or rightmostpart*)
      Array.iteri
        (fun i term ->
          if not !assigned && AstUtil.PredSet.mem (AstUtil.proposition_of_lit x) term then 
            begin
              parts.(i) <- x::(parts.(i));
              assigned := true
            end
        ) props;
  in
    List.iter process mixed;
    Array.to_list parts

(** LA and EUF are equalities interpolating theories
 *  so ti is possible the mkae terms local if an equality is not AB-pure
 * @param theory that deduced the equality
 * @param side is a function that maps an expr to its side: A/B/Mixed
 * @param common_var variables common to A and B
 * @param common_sym fct symbols common to A and B
 * @param a_eq EUF cstr from A
 * @param a_li LA cstr from A
 * @param b_eq EUF cstr from B
 * @param b_li LA cstr from B
 * @param eq the equality to 'localize'
 *)
let make_deduc_local th side common_var common_sym a_eq a_li b_eq b_li eq =
  Message.print Message.Debug (lazy("common var are: "^(Utils.string_list_cat ", "(List.map AstUtil.print_expr common_var))));
  Message.print Message.Debug (lazy("common sym are: "^(Utils.string_list_cat ", " common_sym)));
  Message.print Message.Debug (lazy("for "^(AstUtil.print eq)));
  let make_eq_local_LA ea eb =
    let m = SatLI.find_common_expr (And (a_li @ b_li)) ea common_var common_sym in
      Message.print Message.Debug (lazy("middle term is: "^(AstUtil.print_expr m)));
      let eq_a = AstUtil.order_eq (Eq(ea,m)) in
      let eq_b = AstUtil.order_eq (Eq(eb,m)) in
        [(A, eq_a);(B, eq_b)]
  in
  let make_eq_local_EUF ea eb =
    let a_eq = List.filter (fun x -> match x with Eq _ -> true | _ -> false) a_eq in 
    let b_eq = List.filter (fun x -> match x with Eq _ -> true | _ -> false) b_eq in 
    let m = SatUIF.find_common_expr (And a_eq) (And b_eq) ea eb common_var common_sym in
      Message.print Message.Debug (lazy("middle term is: "^(AstUtil.print_expr m)));
      let eq_a = AstUtil.order_eq (Eq(ea,m)) in
      let eq_b = AstUtil.order_eq (Eq(eb,m)) in
        [(A, eq_a);(B, eq_b)]
  in
    match eq with
    | Eq (e1,e2) as eq ->
      begin
        match (side e1, side e2) with
        | (A,A) | (A,Mixed) | (Mixed,A) -> [(A, eq)]
        | (B,B) | (Mixed,B) | (B,Mixed) | (Mixed,Mixed) -> [(B, eq)]
        | (A,B) ->
          begin
            match th with
            | NelsonOppen.LI -> make_eq_local_LA e1 e2
            | NelsonOppen.UIF -> make_eq_local_EUF e1 e2
            | _ -> failwith "Interpolate, make_deduc_local: theory(1)"
          end
        | (B,A) ->
          begin
            match th with
            | NelsonOppen.LI -> make_eq_local_LA e2 e1
            | NelsonOppen.UIF -> make_eq_local_EUF e2 e1
            | _ -> failwith "Interpolate, make_deduc_local: theory(2)"
          end
      end
    | _ -> failwith "Interpolate, make_deduc_local: expected EQ"

(** buids a partial interpolant from an unsat formula with Nelson Oppen style deduced equalities
 * @param a_terms is the set of terms present in A
 * @param b_terms is the set of terms present in B
 * @param core is the unsat formula
 * @param theory is the theory that find the contradiction
 * @param eq_deduced is a list is deduced equalities (from first to last) with the theory that leads to the deduction
 *)
let partial_interpolant a_prop b_prop (core, theory, eq_deduced) =
  Message.print Message.Debug (lazy("processing core: "^(AstUtil.print core)));
  let core_lst = match core with
    | And lst -> lst
    | _ -> failwith "Interpolate, process_core: expected And"
  in
  let (a_part, b_part) = match splitN_unsat_cores_set [a_prop;b_prop] core_lst with 
    | x::y::[] -> (x,y)
    | _ -> failwith "Interpolate, process_core: error in splitN"
  in
  Message.print Message.Debug (lazy("A part: "^(AstUtil.print (And a_part))));
  Message.print Message.Debug (lazy("B part: "^(AstUtil.print (And b_part))));
  let oa_part = OrdSet.list_to_ordSet a_part in
  let ob_part = OrdSet.list_to_ordSet b_part in
  let (a_part, b_part) = (OrdSet.substract oa_part ob_part, ob_part) in (*follows the projection def of CADE05-interpolants*)

  let a_vars = AstUtil.get_var (And a_part) in
  let b_vars = AstUtil.get_var (And b_part) in
  let common_var = OrdSet.intersection a_vars b_vars in
  let a_sym = AstUtil.get_fct_sym (And a_part) in
  let b_sym = AstUtil.get_fct_sym (And b_part) in
  let common_sym = OrdSet.intersection a_sym b_sym in
    Message.print Message.Debug (lazy("common var are: "^(Utils.string_list_cat ", "(List.map AstUtil.print_expr common_var))));
    Message.print Message.Debug (lazy("common sym are: "^(Utils.string_list_cat ", " common_sym)));

  let side expr =
    match (AstUtil.only_vars_and_symbols a_vars a_sym (Eq (expr, Constant 0.0)),
           AstUtil.only_vars_and_symbols b_vars b_sym (Eq (expr, Constant 0.0))) with
    | (true, true) -> Mixed
    | (true, false) -> A
    | (false, true) -> B
    | (false, false) -> failwith ("Interpolate: "^(AstUtil.print_expr expr)^" belongs to no side.")
  in

  let a_part_eq = ref (List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) a_part) in
  let a_part_li = ref (List.filter (fun x -> match x with | Not _ -> false | _ -> true) a_part) in
  let b_part_eq = ref (List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) b_part) in
  let b_part_li = ref (List.filter (fun x -> match x with | Not _ -> false | _ -> true) b_part) in

  (* partial interplants for  A /\ B /\ ¬eq |- false *)
  let process_deduction (th, eq) =
    Message.print Message.Debug (lazy("process deduction: "^(AstUtil.print eq)));
    match eq with
    | Eq (e1,e2) as eq ->
      begin
        let queries = make_deduc_local th side common_var common_sym !a_part_eq !a_part_li !b_part_eq !b_part_li eq in
        let compute_it (s, eq) =
          Message.print Message.Debug (lazy("compute_it for : "^(AstUtil.print eq)));
          match th with
          | NelsonOppen.LI ->
          (*| LA ->*)
          (* for LA one of the two side only is non-trivial *)
            begin
              let (e1,e2) = match eq with
                | Eq(e1,e2) -> (e1,e2)
                | _ -> failwith "Interpolate, compute_it: not Eq !?"
              in
                if s = A then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And(Lt(e1,e2)::!a_part_li); And !b_part_li] in
                    let lst2 = ClpLI.interpolate_clp [And(Lt(e2,e1)::!a_part_li); And !b_part_li] in
                    let it =  AstUtil.simplify  (Or [List.hd lst1; List.hd lst2]) in
                      (A, it)
                  end
                else if s = B then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e1,e2)::!b_part_li)] in
                    let lst2 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e2,e1)::!b_part_li)] in
                    let it =  AstUtil.simplify  (And [List.hd lst1; List.hd lst2]) in
                      (B, it)
                  end
                else
                  begin
                    assert(false)
                  end
            end
          | NelsonOppen.UIF ->
          (*| EUF ->*)
            begin
              if s = A then
                (A, Or (SatUIF.interpolate_euf true eq (And !a_part_eq) (And !b_part_eq)))
              else
                (B, And (SatUIF.interpolate_euf false eq (And !a_part_eq) (And !b_part_eq)))
            end
          | _ -> failwith "Interpolate, partial_interpolant: theory ??"
        in
        let new_it = List.map compute_it queries in
          Message.print Message.Debug (lazy("deduction its: "^(Utils.string_list_cat ", "(List.map (fun (x,y) -> (side_to_string x)^" "^(AstUtil.print y)) new_it))));
          List.iter2
            (fun (s, eq) (_s, it) -> match s with
              | A -> ( a_part_eq := eq::!a_part_eq; a_part_li := eq::!a_part_li )
              | B -> ( b_part_eq := eq::!b_part_eq; b_part_li := eq::!b_part_li )
              | Mixed ->
                begin
                  assert(s=_s);
                  assert(th = NelsonOppen.LI);
                  match (eq,it) with
                  | (Eq(ea,eb),Lt(e1,e2)) ->
                    let eqa = AstUtil.order_eq (Eq(ea,e1)) in
                      (a_part_eq := eqa::!a_part_eq; a_part_li := eqa::!a_part_li);
                    let eqb = AstUtil.order_eq (Eq(eb,e1)) in
                    ( b_part_eq := eqb::!b_part_eq; b_part_li := eqb::!b_part_li )
                  | _ -> failwith "Interpolate, partial_interpolant: about LI middle term"
                end)
            queries new_it;
          (th, new_it)
      end
    | err -> failwith ("Interpolate, partial_interpolant: deduction is not an equality -> "^(AstUtil.print err))
  in
  let its = List.map process_deduction eq_deduced in
  let final_it = match theory with
    | NelsonOppen.UIF (*EUF*) -> Dag.interpolate_eq (And !a_part_eq) (And !b_part_eq)
    | NelsonOppen.LI (*LA*) ->  List.hd (ClpLI.interpolate_clp [And !a_part_li; And !b_part_li])
    | _ -> failwith "Interpolate, partial_interpolant: theory ?!?"
  in
    (*recompose using the inductive definition*)
  let split_side lst =
    List.fold_left
      (fun (accA,accB,accMixed) (s,it) -> match s with
        | A -> (it::accA, accB, accMixed)
        | B -> (accA, it::accB, accMixed)
        | Mixed -> (accA, accB, it::accMixed)
      )
      ([],[], []) lst
  in
  let it = List.fold_right
      (fun (th,lst) it ->
        let (a_its, b_its, mixed_its) = split_side lst in
          if th = NelsonOppen.UIF then
            begin
              assert(mixed_its = []);
              And ((Or (it::a_its))::b_its)
            end
          else
            begin
              assert(th=NelsonOppen.LI);
              match (a_its, b_its, mixed_its) with
              | (lst,[],[]) -> Or (it::lst)
              | ([],lst,[]) -> And (it::lst)
              | ([],[],[Lt(t_m, t_p)]) -> assert(false) (*Or [And [it;AstUtil.order_eq (Eq(t_p,t_m))]; Lt(t_m,t_p)]*)
              | (a,b,[]) ->
                begin
                  (*Mixed queries*)
                  let relevant = List.filter(fun x -> match x with Lt(e1,e2) -> true | _ -> false) a in
                    match relevant with
                    | Lt(e1,e2)::_ -> Or [(And [it;AstUtil.order_eq (Eq(e1,e2))]); Lt(e1,e2)]
                    | [] -> it
                    | _ -> failwith "Interpolate, partial_interpolant: unreachable part!!"
                end
              | (a,b,c) ->
                failwith ("Interpolate, partial_interpolant: LA interpolants A: "
                  ^(Utils.string_list_cat ", "(List.map AstUtil.print a))
                  ^" B: "^(Utils.string_list_cat ", "(List.map AstUtil.print b))
                  ^" M: "^(Utils.string_list_cat ", "(List.map AstUtil.print c)))
            end
      )
      its final_it 
  in 
    AstUtil.simplify it

(****************************)
(***** experimental code ****)
(*TODO finish and test*)
(*
let partial_interpolant_lst lst_prop (core, theory, eq_deduced) =
  Message.print Message.Debug (lazy("processing core: "^(AstUtil.print core)));
  let core_lst = match core with
    | And lst -> lst
    | _ -> failwith "Interpolate, process_core: expected And"
  in
  let lst_part = splitN_unsat_cores_set lst_prop core_lst in
  
  let make_common lst =
    let a_side =
      let (lst,_) = List.fold_left
        (fun (res,acc) x -> let new_set = OrdSet.union x acc in (new_set::res, new_set) )
        ([], []) lst
      in
        List.rev (List.tl lst)
    in
    let b_side =
      let (lst,_) = List.fold_right
        (fun x (res,acc) -> let new_set = OrdSet.union x acc in (new_set::res, new_set) )
        lst ([], [])
      in
        List.tl lst
    in
      List.map2 (fun a b -> OrdSet.intersection a b) a_side b_side
  in
  let lst_vars = List.map (fun x -> AstUtil.get_var (And x)) lst_part in
  let common_var = make_common lst_vars in
  let lst_sym = List.map (fun x -> AstUtil.get_fct_sym (And x)) lst_part in
  let common_sym = make_common lst_sym in

  (* returns a pairs i,j where i is the leftmost part expr is in, and j the rightmost *)
  let side expr =
    let _min = ref 100000 in
    let _max = ref (-1) in
    let _ = List.fold_left2
        (fun i vars syms ->
          if AstUtil.only_vars_and_symbols vars syms (Eq (expr, Constant 0.0)) then
            begin
              _min := min !_min i;
              _max := max !_max i;
            end;
          i + 1
        ) 0 lst_vars lst_sym
    in
      assert(!_min >= 0);
      assert(!_max >= 0);
      assert(!_max >= !_min);
      (!_min,!_max)
  in

  let part_eq = Array.of_list (List.map (fun part -> List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) part) lst_part) in
  let part_li = Array.of_list (List.map (fun part -> List.filter (fun x -> match x with | Not _ -> false | _ -> true) part) lst_part) in

  (*TODO*)
  (* partial interplants for  A /\ B /\ ¬eq |- false *)
  let process_deduction (th, eq) =
    Message.print Message.Debug (lazy("process deduction: "^(AstUtil.print eq)));
    match eq with
    | Eq (e1,e2) as eq ->
      begin
        let queries = make_deduc_local_lst th side common_var common_sym part_eq part_li eq in
        let compute_it (s, eq) =
          Message.print Message.Debug (lazy("compute_it for : "^(AstUtil.print eq)));
          match th with
          | NelsonOppen.LI ->
          (*| LA ->*)
          (* for LA one of the two side only is non-trivial *)
            begin
              let (e1,e2) = match eq with
                | Eq(e1,e2) -> (e1,e2)
                | _ -> failwith "Interpolate, compute_it: not Eq !?"
              in
                if s = A then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And(Lt(e1,e2)::!a_part_li); And !b_part_li] in
                    let lst2 = ClpLI.interpolate_clp [And(Lt(e2,e1)::!a_part_li); And !b_part_li] in
                    let it =  AstUtil.simplify  (Or [List.hd lst1; List.hd lst2]) in
                      (A, it)
                  end
                else if s = B then
                  begin
                    let lst1 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e1,e2)::!b_part_li)] in
                    let lst2 = ClpLI.interpolate_clp [And !a_part_li; And (Lt(e2,e1)::!b_part_li)] in
                    let it =  AstUtil.simplify  (And [List.hd lst1; List.hd lst2]) in
                      (B, it)
                  end
                else
                  begin
                    assert(false)
                  end
            end
          | NelsonOppen.UIF ->
          (*| EUF ->*)
            begin
              if s = A then
                (A, Or (SatUIF.interpolate_euf true eq (And !a_part_eq) (And !b_part_eq)))
              else
                (B, And (SatUIF.interpolate_euf false eq (And !a_part_eq) (And !b_part_eq)))
            end
          | _ -> failwith "Interpolate, partial_interpolant: theory ??"
        in
        let new_it = List.map compute_it queries in
          Message.print Message.Debug (lazy("deduction its: "^(Utils.string_list_cat ", "(List.map (fun (x,y) -> (side_to_string x)^" "^(AstUtil.print y)) new_it))));
          List.iter2
            (fun (s, eq) (_s, it) -> match s with
              | A -> ( a_part_eq := eq::!a_part_eq; a_part_li := eq::!a_part_li )
              | B -> ( b_part_eq := eq::!b_part_eq; b_part_li := eq::!b_part_li )
              | Mixed ->
                begin
                  assert(s=_s);
                  assert(th = NelsonOppen.LI);
                  match (eq,it) with
                  | (Eq(ea,eb),Lt(e1,e2)) ->
                    let eqa = AstUtil.order_eq (Eq(ea,e1)) in
                      (a_part_eq := eqa::!a_part_eq; a_part_li := eqa::!a_part_li);
                    let eqb = AstUtil.order_eq (Eq(eb,e1)) in
                    ( b_part_eq := eqb::!b_part_eq; b_part_li := eqb::!b_part_li )
                  | _ -> failwith "Interpolate, partial_interpolant: about LI middle term"
                end)
            queries new_it;
          (th, new_it)
      end
    | err -> failwith ("Interpolate, partial_interpolant: deduction is not an equality -> "^(AstUtil.print err))
  in
  let its = List.map process_deduction eq_deduced in
  let final_it = match theory with
    | NelsonOppen.UIF (*EUF*) -> Dag.interpolate_eq common_var common_sym (AstUtil.to_list part_eq)
    | NelsonOppen.LI (*LA*) ->  ClpLI.interpolate_clp (Array.to_list part_li)
    | _ -> failwith "Interpolate, partial_interpolant: theory ?!?"
  in
    (*recompose using the inductive definition*)
  let split_side lst =
    List.fold_left
      (fun (accA,accB,accMixed) (s,it) -> match s with
        | A -> (it::accA, accB, accMixed)
        | B -> (accA, it::accB, accMixed)
        | Mixed -> (accA, accB, it::accMixed)
      )
      ([],[], []) lst
  in
  let it = List.fold_right
      (fun (th,lst) it ->
        let (a_its, b_its, mixed_its) = split_side lst in
          if th = NelsonOppen.UIF then
            begin
              assert(mixed_its = []);
              And ((Or (it::a_its))::b_its)
            end
          else
            begin
              assert(th=NelsonOppen.LI);
              match (a_its, b_its, mixed_its) with
              | (lst,[],[]) -> Or (it::lst)
              | ([],lst,[]) -> And (it::lst)
              | ([],[],[Lt(t_m, t_p)]) -> assert(false) (*Or [And [it;AstUtil.order_eq (Eq(t_p,t_m))]; Lt(t_m,t_p)]*)
              | (a,b,[]) ->
                begin
                  (*Mixed queries*)
                  let relevant = List.filter(fun x -> match x with Lt(e1,e2) -> true | _ -> false) a in
                    match relevant with
                    | Lt(e1,e2)::_ -> Or [(And [it;AstUtil.order_eq (Eq(e1,e2))]); Lt(e1,e2)]
                    | [] -> it
                    | _ -> failwith "Interpolate, partial_interpolant: unreachable part!!"
                end
              | (a,b,c) ->
                failwith ("Interpolate, partial_interpolant: LA interpolants A: "
                  ^(Utils.string_list_cat ", "(List.map AstUtil.print a))
                  ^" B: "^(Utils.string_list_cat ", "(List.map AstUtil.print b))
                  ^" M: "^(Utils.string_list_cat ", "(List.map AstUtil.print c)))
            end
      )
      its final_it 
  in 
    AstUtil.simplify it
*)

(******************************************************)
(*******  WARNING:  DEPRECATED CODE  ******************)
(** need rewrite! it does not need a proof, but DNF ***)
(** can be good to interpolant formula in DNF *********)
(******************************************************)

let build_interpolant a b cores_with_info =
  
  let a_term = AstUtil.get_subterm_nnf a in
    Message.print Message.Debug (lazy("a_term: "^(Utils.string_list_cat ", " (List.map AstUtil.print a_term))));

  let b_term = AstUtil.get_subterm_nnf b in
    Message.print Message.Debug (lazy("b_term: "^(Utils.string_list_cat ", " (List.map AstUtil.print b_term))));

  let a_dnf = match AstUtil.dnf a with 
    | Or lst -> List.map (fun x -> match x with | And l -> OrdSet.list_to_ordSet l | _ -> failwith "Interpolate: DNF(2)") lst
    | _ ->  failwith "interpolate: DNF"
  in
  let b_dnf = match AstUtil.dnf b with 
    | Or lst -> List.map (fun x -> match x with | And l -> OrdSet.list_to_ordSet l | _ -> failwith "Interpolate: DNF(2)") lst
    | _ ->  failwith "interpolate: DNF"
  in

  (*TODO improve*)
  let find_matching_assignement a_only b_only common =
    let b_possible = List.filter (fun l -> (OrdSet.intersection b_only l) = b_only) b_dnf in
    let how_many l = List.length (OrdSet.intersection l common) in
    let rec find_max lst =
      snd (List.fold_left (fun (n,better) l -> let nn = how_many l in if nn > n then (nn,l) else (n,better)) (-1,[]) lst)
    in
    let rec find_min lst =
      snd (List.fold_left (fun (n,better) l -> let nn = how_many l in if nn < n then (nn,l) else (n,better)) (1000000000,[]) lst)
    in
    let b_max = find_max b_possible in
    let diff = OrdSet.union a_only (OrdSet.substract common b_max) in
    let a_possible = List.filter (fun l -> (OrdSet.intersection diff l) = diff) a_dnf in
    let a_min = find_min a_possible in
      (OrdSet.intersection (OrdSet.union a_only common) a_min, OrdSet.intersection (OrdSet.union b_only common) b_max)
  in
  
  (*to keep partial interpolant*)
  let a_parts = ref [] in
  let it_table = Hashtbl.create 13 in
  (*****************************)

  (*compute interpolant for each core*)
  let process_core  (core, theory, eq_deduced) =
    Message.print Message.Debug (lazy("processing core: "^(AstUtil.print core)));
    
    let core_lst = match core with
      | And lst -> lst
      | _ -> failwith "Interpolate, process_core: expected And"
    in
    let (a_part, b_part) = match splitN_unsat_cores [a_term;b_term] core_lst with 
      | x::y::[] -> (x,y)
      | _ -> failwith "Interpolate, process_core: error in splitN"
    in
    let oa_part = OrdSet.list_to_ordSet a_part in
    let ob_part = OrdSet.list_to_ordSet b_part in
    let common_term = OrdSet.intersection  oa_part ob_part in
    let (a_part, b_part) = 
      if common_term = [] then
          (a_part, b_part)
      else
         find_matching_assignement (OrdSet.substract oa_part common_term) (OrdSet.substract ob_part common_term) common_term
    in

    let a_part_expr = AstUtil.get_expr_deep (And a_part) in
    let b_part_expr = AstUtil.get_expr_deep (And b_part) in
      Message.print Message.Debug (lazy("A part : "^(Utils.string_list_cat ", "(List.map AstUtil.print a_part))));
      Message.print Message.Debug (lazy("B part : "^(Utils.string_list_cat ", "(List.map AstUtil.print b_part))));
    let side expr =
      match (List.mem expr a_part_expr , List.mem expr b_part_expr) with
      | (true, true) -> Mixed
      | (true, false) -> A
      | (false, true) -> B
      | (false, false) -> failwith ("Interpolate: "^(AstUtil.print_expr expr)^" belongs to no side.")
    in


    let graph_a = new Dag.dag (a_part_expr)  in
    let a_part_eq = List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) a_part in
    let a_part_li = List.filter (fun x -> match x with | Not _ -> false | _ -> true) a_part in
    let _ = graph_a#is_satisfiable (And a_part_eq) (*inject cstr*) in
    
    let graph_b = new Dag.dag (b_part_expr)  in
    let b_part_eq = List.filter (fun x -> match x with | Leq _ | Lt _ -> false | _ -> true) b_part in
    let b_part_li = List.filter (fun x -> match x with | Not _ -> false | _ -> true) b_part in
    let _ = graph_b#is_satisfiable (And b_part_eq) (*inject cstr*) in

    let common_var = OrdSet.intersection (OrdSet.list_to_ordSet (AstUtil.get_var (And a_part))) (OrdSet.list_to_ordSet (AstUtil.get_var (And b_part)))in
      Message.print Message.Debug (lazy("common var are: "^(Utils.string_list_cat ", "(List.map AstUtil.print_expr common_var))));
    let common_sym = OrdSet.intersection (AstUtil.get_fct_sym (And a_part)) (AstUtil.get_fct_sym (And b_part))in
      Message.print Message.Debug (lazy("common sym are: "^(Utils.string_list_cat ", " common_sym)));
    (*let common_expr = OrdSet.intersection (OrdSet.list_to_ordSet a_part_expr) (OrdSet.list_to_ordSet b_part_expr) in*)
    a_parts := OrdSet.union [a_part] !a_parts;
    
    (*already applied eq -> for LI ...*)
    let applied = ref [] in
    let applied_to_a_b theory = match theory with
      | NelsonOppen.LI ->
        List.fold_left 
          (fun (accA, accB) (part, eq) ->
            match part with
            | A -> (eq::accA, accB)
            | B -> (accA, eq::accB)
            | Mixed -> failwith "Interpolate, applied_to_a_b: found Mixed"
          ) (a_part_li, b_part_li) !applied
      | NelsonOppen.UIF ->
        List.fold_left 
          (fun (accA, accB) (part, eq) ->
            match part with
            | A -> (eq::accA, accB)
            | B -> (accA, eq::accB)
            | Mixed -> failwith "Interpolate, applied_to_a_b: found Mixed"
          ) (a_part_eq, b_part_eq) !applied
      | _ -> failwith "Interpolate: apply unsupported theory"
    in
    let apply ((side,eq) as seq) =
      Message.print Message.Debug (lazy("applying: "^(AstUtil.print eq)));
      applied := seq::!applied; 
      match side with (*can introduce new term -> linear combinations*)
      | A -> graph_a#create_and_add_constr eq 
      | B -> graph_b#create_and_add_constr eq 
      | Mixed -> failwith "Interpolate, apply: found Mixed"
    in

    let neg_eq eq = match eq with
      | Eq (e1,e2) -> (Lt(e1,e2),Lt(e2,e1))
      | e -> failwith ("Interpolate, neg_ls: found "^(AstUtil.print e))
    in

  
    let li_flag = ref false in
    let li_it_for_deduc (side, eq) = match side with
      | A ->
        begin
          let (case1,case2) = neg_eq eq in
          let (a_part,b_part) = applied_to_a_b NelsonOppen.LI in
          let lst1 = ClpLI.interpolate_clp [And(case1::a_part); And b_part] in
          let lst2 = ClpLI.interpolate_clp [And(case2::a_part); And b_part] in
          let it = AstUtil.simplify  (Or [List.hd lst1; List.hd lst2]) in
            (A, it)
        end
        | B ->
        begin
          let (case1,case2) = neg_eq eq in
          let (a_part,b_part) = applied_to_a_b NelsonOppen.LI in
          let lst1 = ClpLI.interpolate_clp [And a_part; And (case1::b_part)] in
          let lst2 = ClpLI.interpolate_clp [And a_part; And (case2::b_part)] in
          let it = AstUtil.simplify  (And [List.hd lst1; List.hd lst2]) in
            (B, it)
        end
      | Mixed -> failwith "Interpolate, li_it_for_deduc: found Mixed"
    in
    
    (* does not change the underlying graphs *)
    let uif_it_for_deduc (side, eq) = match side with
      | A ->
        begin
          Message.print Message.Debug (lazy("uif_it_for_deduc A: "^(AstUtil.print eq)));
          (*TODO the new term is congruent, and Dag don't do congruence...*)(*BUG BUG*)
          (*if exists ok, else goes down to the args*)
          graph_a#create_needed_nodes eq;
          graph_a#add_neq (Not eq);
          let it = Dag.interpolate_from_graph graph_a graph_b in
            graph_a#remove_neq (Not eq);
            (A, it)
        end
        | B ->
        begin
          Message.print Message.Debug (lazy("uif_it_for_deduc B: "^(AstUtil.print eq)));
          graph_b#create_needed_nodes eq;
          graph_b#add_neq (Not eq);
          let it = Dag.interpolate_from_graph graph_a graph_b in
            graph_b#remove_neq (Not eq);
            (B, it)
        end
      | Mixed -> failwith "Interpolate, uif_it_for_deduc: found Mixed"
    in

    let make_eq_local ea eb =
       try
         let m = Dag.find_common_expr_graph ea eb graph_a graph_b common_var common_sym in
         let eq_a = AstUtil.order_eq (Eq(ea,m)) in
         let eq_b = AstUtil.order_eq (Eq(eb,m)) in
           [(B, eq_b);(A, eq_a)]
       with Not_found -> 
           begin
             (*reaching this means that decudction comes from LA*)
             let all_cstr = 
               let (a_l, b_l) = applied_to_a_b NelsonOppen.LI in
                 And (a_l @ b_l)
             in
             let m = SatLI.find_common_expr all_cstr ea common_var common_sym in
             let eq_a = AstUtil.order_eq (Eq(ea,m)) in
             let eq_b = AstUtil.order_eq (Eq(eb,m)) in
               li_flag := true; (*HACK !!!*)
               [(A, eq_a);(B, eq_b)]
           end
    in
    
    let make_deduc_local eq = match eq with
        | Eq (e1,e2) as eq ->
          begin
            match (side e1, side e2) with
            | (A,A) | (A,Mixed) | (Mixed,A) -> [(A, eq)]
            | (B,B) | (Mixed,B) | (B,Mixed) | (Mixed,Mixed) -> [(B, eq)]
            | (A,B) -> make_eq_local e1 e2
            | (B,A) -> make_eq_local e2 e1
          end
      | _ -> failwith "Interpolate, li_it_for_deduc: expected EQ"
    in
    
    let it_for_deduct query_fct eq =
      match make_deduc_local eq with
      | x::y::[] as lst -> (query_fct x, lst)(*make_deduc_local makes it such that pinking the first is sufficient*)
      | x::[] as lst -> (query_fct x, lst)
      | _ -> failwith "Interpolate, it_for_deduct: ..."
    in

    let process_deduction ((_, eq) as ded) =
      Message.print Message.Debug (lazy("processing deduction: "^(AstUtil.print eq)));
      match ded with
      | (NelsonOppen.LI, eq) ->
        begin
          let (it,eq_lst) = it_for_deduct li_it_for_deduc eq in
            List.iter apply eq_lst;
            if !li_flag then (*HACK !!*)
              begin
                li_flag := false;
                match it with
                  | (A,Lt (e1,e2)) -> [(it,Some( AstUtil.order_eq (Eq(e1,e2))))]
                  | (_, True) -> [((B,True),None)]
                  | (A,err) -> failwith ("Interpolate, process_deduction, eq_to_keep: found A, "^(AstUtil.print err))
                  | (B,err) -> failwith ("Interpolate, process_deduction, eq_to_keep: found B, "^(AstUtil.print err))
                  | (Mixed,err) -> failwith ("Interpolate, process_deduction, eq_to_keep: found Mixed, "^(AstUtil.print err))
              end
            else
              begin
                [(it,None)]
              end
        end
      | (NelsonOppen.UIF, (Eq((Application(s1, args1) as e1), (Application(s2,args2) as e2)) as eq) ) ->
        begin (*arguments*)
          (*side of args is same as congruence*)
          let (side1,side2) =
              begin
                match (side e1, side e2) with
                | (A,A) | (A,Mixed) | (Mixed,A) -> (A, A)
                | (B,B) | (Mixed,B) | (B,Mixed) | (Mixed,Mixed) -> (B,B)
                | s -> s
              end
          in
          let args_for_top_fct = ref [] in
          let args_it_tmp = List.map2
            (fun x y -> if side1 = side2 then
                begin
                  let seq = (side1, AstUtil.order_eq (Eq (x,y))) in
                    ((uif_it_for_deduc seq), [seq])
                end
              else
                begin
                  let (ea,eb) = if side1 = A then (x,y) else (y,x) in
                    Message.print Message.Debug (lazy("from A : "^(AstUtil.print_expr ea)));
                    Message.print Message.Debug (lazy("from B : "^(AstUtil.print_expr eb)));
                    match make_eq_local ea eb with
                    | ((_,Eq(x1,x2)) as x)::((_,Eq(y1,y2)))::[] as lst ->
                      begin
                        begin
                          match ((x1=y1)||(x1=y2),(x2=y1)||(x2=y2)) with
                          | (true,_) -> args_for_top_fct := x1::!args_for_top_fct
                          | (_,true) -> args_for_top_fct := x2::!args_for_top_fct
                          | _ -> failwith "Interpolate, process_deduction: no middle term!!"
                        end;
                        (uif_it_for_deduc x, lst)(*make_deduc_local makes it such that picking the first is sufficient*)
                      end
                    | _ -> failwith "Interpolate, process_deduction: expected 2"
                end
            ) args1 args2
          in
          let args_it =
            List.fold_left
              (fun acc (it, eq_lst) ->
                List.iter apply eq_lst;
                (it,None)::acc
              ) [] args_it_tmp
          in
            (*List.iter apply eq_lst;*)
            if side1 = side2 then apply (side1, eq)
            else
              begin
                let m = Application(s1, List.rev !args_for_top_fct) in
                 apply (side1, AstUtil.order_eq (Eq(e1,m)));
                 apply (side2, AstUtil.order_eq (Eq(e2,m)))
              end;
            args_it
        end
      | (NelsonOppen.UIF, _) -> failwith "Interpolate, process_deduction: UIF match error"
      | _ -> failwith "deduction from unsupported theory"
    in
    
    let partial_deduced_it = List.flatten (List.map process_deduction eq_deduced) in
    let print_it ((side, it), _)= match side with | A -> "A:"^(AstUtil.print it) | B -> "B:"^(AstUtil.print it) | Mixed -> "Mixed:"^(AstUtil.print it) in
      Message.print Message.Debug (lazy("partial_deduced_it are: "^(Utils.string_list_cat ", " (List.map print_it partial_deduced_it))));
    let recompose_final_it it = 
      List.fold_right
        (fun ((side, pit), eq_opt) it ->
          match eq_opt with
          | None -> (*normal case*)
            begin
              match side with
              | A -> Or [it;pit]
              | B -> And [it;pit]
              | Mixed -> failwith "Interpolate, recompose_final_it: mixed interpolant!"
            end
          | Some eq -> (*LA case*)
            begin
              Or [(And [it;eq]); pit]
            end
        )
        partial_deduced_it it
    in

    let final_it = match theory with
      | NelsonOppen.LI ->
        begin
          let (a_part,b_part) = applied_to_a_b NelsonOppen.LI in
          let it = List.hd (ClpLI.interpolate_clp [And a_part; And b_part]) in
            Message.print Message.Debug (lazy("last it is: "^(AstUtil.print it)));
            recompose_final_it it
        end
      | NelsonOppen.UIF ->
        begin
          let it = Dag.interpolate_from_graph graph_a graph_b in
            Message.print Message.Debug (lazy("last it is: "^(AstUtil.print it)));
            recompose_final_it it
        end
      | NelsonOppen.BOOL ->
        begin
          match a_part with
          | [] -> True
          | x::[] -> x
          | x::y::[] -> False
          | _ -> failwith "Interpolate: direct contradiction with more than two elements !?!"
        end
      | _ -> failwith "interpolate: SAT or unsupported theory"
    in
      Hashtbl.add it_table a_part final_it

  in
    List.iter process_core cores_with_info;

    (*build final interpolant*)
    let a_dnf_parts = List.map (fun olst -> 
          List.filter (fun l ->
            let ol = OrdSet.list_to_ordSet l in
              (OrdSet.intersection ol olst) = ol
            ) !a_parts
      ) a_dnf
    in
    (*let a_dnf_parts = List.filter (fun l -> l <> []) a_dnf_parts in*)
      AstUtil.simplify (Or (List.map (fun l -> And (List.map (fun x -> And (Hashtbl.find_all it_table x)) l)) a_dnf_parts))

let interpolate a b =
  let a = AstUtil.simplify a in
  let b = AstUtil.simplify b in
  let ab = AstUtil.normalize_only (And [a; b]) in
  let cores_with_info =
    if AstUtil.is_conj_only a && AstUtil.is_conj_only b then
      begin
        Message.print Message.Debug (lazy "Interpolate: formula is conj only");
        [NelsonOppen.unsat_LIUIF (AstUtil.simplify ab)]
      end
    else
      begin
        Message.print Message.Debug (lazy "Interpolate: using sat solver");
        SatPL.unsat_cores_LIUIF ab
      end
  in
    build_interpolant a b cores_with_info
(************************************************)
(************************************************)
(************************************************)
(************************************************)

(*end of tree: what kind of clause*)
type eot_t = ACl (*A clause*)
           | BCl (*B clause*)
           | NCl of int (*# clause for path interpolation*)
           | ThCl of predicate * NelsonOppen.contradiction_in * ((NelsonOppen.contradiction_in * predicate) list)
           | NotCl (*Not a clause*)

(** build the interpolant by recurssing in the proof
 * @param a
 * @param b
 * @param proof a resolution proof, see dpllProof.ml
 * @param cores_with_info list of unsat cores + theory + eq deductions
 *)
let recurse_in_proof a b proof cores_with_info =
  let clause_to_side = Hashtbl.create 1000 in
  let add_disj_to_side disj side =
    let lits = 
      match disj with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (1) "^(AstUtil.print err))
    in
      Hashtbl.add clause_to_side lits side
  in
  let add_core (core,th,info) =
    let lits = 
      match SatPL.reverse core with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (2) "^(AstUtil.print err))
    in
      Hashtbl.add clause_to_side lits (ThCl (core,th,info))
  in
  let lookup_cl cl =
    try
      Hashtbl.find clause_to_side (cl#literals)
    with Not_found -> NotCl
  in
  let _ = match a with
    | And lst -> List.iter (fun x -> add_disj_to_side x ACl) lst
    | _ -> failwith "Interpolate, build_trie: not in CNF (1)"
  in
  let _ = match b with
    | And lst -> List.iter (fun x -> add_disj_to_side x BCl) lst
    | _ -> failwith "Interpolate, build_trie: not in CNF (2)"
  in
  let _ = List.iter (fun x -> add_core x) cores_with_info in

  (*cache to replicate subproof*)
  let cache = Hashtbl.create 100 in

  let a_prop = AstUtil.get_proposition_set a in
  let b_prop = AstUtil.get_proposition_set b in
  let rec recurse prf = match prf with
    | DpllProof.RPNode (pivot, left, right, result) ->
      if Hashtbl.mem cache result then Hashtbl.find cache result
      else
        begin
          let left_it = recurse left in
          let right_it = recurse right in
          let it = match (AstUtil.PredSet.mem pivot a_prop, AstUtil.PredSet.mem pivot b_prop) with
            | (true, true) ->
              if (DpllProof.get_result left)#has pivot then
                begin
                  assert ((DpllProof.get_result right)#has_not pivot);
                  And [Or [pivot ;left_it]; Or [Not pivot ;right_it]]
                end
              else
                begin
                  assert ((DpllProof.get_result left)#has_not pivot);
                  assert ((DpllProof.get_result right)#has pivot);
                  And [Or [Not pivot ;left_it]; Or [pivot ;right_it]]
                end
            | (true, false) -> Or [left_it; right_it]
            | (false, true) -> And [left_it; right_it]
            | (false, false) -> failwith "Interpolate, recurse_in_proof: pivot does not belong to any side"
          in
            Hashtbl.add cache result it;
            it
        end
    | DpllProof.RPLeaf clause ->
      begin
        match lookup_cl clause with
        | ACl -> False
        | BCl -> True
        | NCl _ -> failwith "Interpolate, recurse_in_proof: NCl when not using path interpolation !!!"
        | ThCl (c,t,i) -> partial_interpolant a_prop b_prop (c,t,i)
        | NotCl -> failwith "Interpolate, recurse_in_proof: leaf of proof in not a clause !!!"
      end
  in
    recurse proof

let interpolate_with_proof a b =
  let a = AstUtil.cnf (AstUtil.simplify a) in
  let b = AstUtil.cnf (AstUtil.simplify b) in
  let a = AstUtil.normalize_only (AstUtil.remove_lit_clash a) in
  let b = AstUtil.normalize_only (AstUtil.remove_lit_clash b) in
  let a_cnf = AstUtil.cnf a in
  let b_cnf = AstUtil.cnf b in
    match (a,b) with
    | (True,_) | (_,False)-> True
    | (False,_)| (_,True) -> False
    | _->
      begin
        if AstUtil.is_conj_only a && AstUtil.is_conj_only b then
          begin
            (*when conj only, bypass the get_unsat_core*)
            Message.print Message.Debug (lazy "Interpolate: formula is conj only");
            let core_with_info =
              NelsonOppen.unsat_LIUIF (AstUtil.normalize_only (And [a; b]))
            in
              build_interpolant a b [core_with_info]
          end
        else
          begin
            let ab = AstUtil.normalize_only (And [a_cnf; b_cnf]) in
              Message.print Message.Debug (lazy "Interpolate: using sat solver and proof");
            let (cores_with_info, proof) = 
              SatPL.unsat_cores_with_proof ab
            in
            let it = recurse_in_proof a_cnf b_cnf proof cores_with_info in
              AstUtil.simplify it
          end
      end

(*******************)
(*experimental code*)
(*TODO finish and test*)
(*
let recurse_in_proof_lst lst proof cores_with_info =
  let clause_to_side = Hashtbl.create 1000 in
  let add_disj_to_side disj side =
    let lits = 
      match disj with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (1) "^(AstUtil.print err))
    in
      Hashtbl.add clause_to_side lits side
  in
  let add_core (core,th,info) =
    let lits = 
      match SatPL.reverse core with
      | Or lst -> OrdSet.list_to_ordSet lst
      | err -> failwith ("Interpolate, clause_to_side: core is not a disj (2) "^(AstUtil.print err))
    in
      Hashtbl.add clause_to_side lits (ThCl (core,th,info))
  in
  let lookup_cl cl =
    try
      Hashtbl.find clause_to_side (cl#literals)
    with Not_found -> NotCl
  in
  let _ = List.fold_left
    (fun i x ->
      let _ = match x with
        | And lst -> List.iter (fun x -> add_disj_to_side x (NCl i)) lst
        | _ -> failwith "Interpolate, build_trie: not in CNF (1)"
      in
        i+1)
    0 lst
  in
  let _ = List.iter (fun x -> add_core x) cores_with_info in

  (*cache to replicate subproof*)
  let cache = Hashtbl.create 100 in

  (*list of pairs each element correspond to a possible cut in the input*)
  let lst_prop = List.map AstUtil.get_proposition_set lst in
  (*TODO assert length = |lst_prop| -1*)
  let ab_lst_prop =
    let a_side =
      let (lst,_) = List.fold_left
        (fun (res,acc) x -> let new_set = AstUtil.PredSet.union x acc in (new_set::res, new_set) )
        ([], AstUtil.PredSet.empty) lst_prop
      in
        List.rev (List.tl lst)
    in
    let b_side =
      let (lst,_) = List.fold_right
        (fun x (res,acc) -> let new_set = AstUtil.PredSet.union x acc in (new_set::res, new_set) )
        lst_prop ([], AstUtil.PredSet.empty)
      in
        List.tl lst
    in
      List.map2 (fun x y -> (x,y)) a_side b_side
  in

  (*recursively build the interpolant from the proof*)
  let rec recurse prf = match prf with
    | DpllProof.RPNode (pivot, left, right, result) ->
      if Hashtbl.mem cache result then Hashtbl.find cache result
      else
        begin
          let left_it = recurse left in
          let right_it = recurse right in
          let rec build_it_lst acc lit rit prop = match (lit,rit,prop) with
            | (left_it::ls, right_it::rs, (a_prop,b_prop)::ps) ->
              begin
                let it =
                  match (AstUtil.PredSet.mem pivot a_prop, AstUtil.PredSet.mem pivot b_prop) with
                  | (true, true) ->
                      if (DpllProof.get_result left)#has pivot then
                        begin
                          assert ((DpllProof.get_result right)#has_not pivot);
                          And [Or [pivot ;left_it]; Or [Not pivot ;right_it]]
                        end
                      else
                        begin
                          assert ((DpllProof.get_result left)#has_not pivot);
                          assert ((DpllProof.get_result right)#has pivot);
                          And [Or [Not pivot ;left_it]; Or [pivot ;right_it]]
                        end
                  | (true, false) -> Or [left_it; right_it]
                  | (false, true) -> And [left_it; right_it]
                  | (false, false) -> failwith "Interpolate, recurse_in_proof: pivot does not belong to any side"
                in
                  build_it_lst (it::acc) ls rs ps
              end
            | ([],[],[]) -> List.rev acc
            | _ -> failwith "Interpolate, interpolate_with_proof_lst: match error (1)"
          in
          let it = build_it_lst [] left_it right_it ab_lst_prop
          in
            Hashtbl.add cache result it;
            it
        end
    | DpllProof.RPLeaf clause ->
      begin
        match lookup_cl clause with
        | NCl i ->
          List.rev (snd (
            List.fold_left
              (fun (n, acc) _ ->
                if i <= n then (n+1, False::acc) else (n+1, True::acc))
              (0,[]) lst_prop))
        | ThCl (c,t,i) -> partial_interpolant_lst lst_prop (c,t,i)
        | NotCl -> failwith "Interpolate, recurse_in_proof: leaf of proof in not a clause !!!"
      end
  in
    recurse proof
*)


(*
let interpolate_with_proof_lst lst =
  let lst = List.map (fun x ->  AstUtil.cnf (AstUtil.simplify x)) lst in
  let lst = List.map (fun x -> AstUtil.normalize_only (AstUtil.remove_lit_clash x)) lst in
  (*TODO trivial cases *)
    begin
      if List.for_all AstUtil.is_conj_only lst then
        begin
          (*when conj only, bypass the get_unsat_core*)
          Message.print Message.Debug (lazy "Interpolate: formula is conj only");
          let core_with_info =
            NelsonOppen.unsat_LIUIF (AstUtil.normalize_only (And lst))
          in
            (*build_interpolant_lst lst [core_with_info]*)
            partial_interpolant_lst lst core_with_info
        end
      else
        begin
          let lst_cnf = List.map AstUtil.cnf lst in
          let whole = AstUtil.normalize_only (And lst_cnf) in
            Message.print Message.Debug (lazy "Interpolate: using sat solver and proof");
          let (cores_with_info, proof) = 
            SatPL.unsat_cores_with_proof whole
          in
          let its = recurse_in_proof_lst lst_cnf proof cores_with_info in
            List.map AstUtil.simplify its
        end
    end
*)