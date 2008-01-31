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

type side = A | B | Mixed

let splitN_unsat_cores terms_lst mixed =
  let terms = Array.of_list terms_lst in
  let parts = Array.make (List.length terms_lst) [] in
  let rec process x =
    Array.iteri
      (fun i term ->
        if OrdSet.mem x term then parts.(i) <- x::(parts.(i));
      ) terms
  in
    List.iter process mixed;
    Array.to_list parts

let is_cst e = match e with
  | Constant _ -> true
  | _ -> false
let allowed_sym sym expr = match expr with
  | Application (s, _) -> (List.mem s sym)
  | _ -> false
let expr_only vars sym expr =
  let rec process expr = match expr with
    | Constant _ -> true
    | Variable _ as v -> List.mem v vars
    | Application (s, lst) -> (List.mem s sym) && (List.for_all process (List.filter (fun x -> not (is_cst x)) lst))
    | Coeff(_, e) -> process e
    | Sum lst -> List.for_all process (List.filter (fun x -> not (is_cst x)) lst)
  in
    process expr
let expr_only_strict vars sym expr = (*force at least one common symbol/var*)
  (not(is_cst expr)) && (expr_only vars sym expr)

let find_middle_term common_var common_sym graph e =
  Message.print Message.Debug (lazy("find middle for: "^(AstUtil.print_expr e)));
  let cc = graph#get_cc in
    Message.print Message.Debug (lazy("cc are: "^(Utils.string_list_cat ", "(List.map (fun x -> "["^(Utils.string_list_cat ", " (List.map AstUtil.print_expr x))^"]") cc))));
  let stack = ref [] in
  let rec get_equiv expr =
  let cur_cc = try List.hd (List.filter (List.mem expr) cc)
    with Failure "hd" -> failwith ((AstUtil.print_expr expr)^" does not belong to any CC.")
  in
    Message.print Message.Debug (lazy("cur_cc is: "^(Utils.string_list_cat ", "(List.map AstUtil.print_expr cur_cc))));
    let lucky = List.filter (if !stack = [] then (expr_only_strict common_var common_sym) else (expr_only common_var common_sym)) cur_cc in
    (*let lucky = List.filter (fun expr -> List.mem expr common_expr) cur_cc in*)
      Message.print Message.Debug (lazy("lucky is: "^(Utils.string_list_cat ", "(List.map AstUtil.print_expr lucky))));
    if List.length lucky > 0 then
      begin
        Some(List.hd lucky)
      end
    else
      (*DFS*)
      begin
        if List.mem expr !stack then
          None (*cycle detection*)
        else
          let possible_term = List.filter (allowed_sym common_sym) cur_cc in
            stack := expr::(!stack);
            let fill_sub expr = match expr with
              | Application (s, lst) ->
                (*TODO if s is not a common symbol*)
                let args = List.map get_equiv lst in
                  if List.for_all (fun x -> x <> None ) args then
                      Some (Application(s, Utils.remove_some args))
                  else None
              | err -> failwith ("Interpolate, fill sub: found "^(AstUtil.print_expr err))
            in
            let rec find_possible lst = match lst with
              | x::xs ->
                begin
                  match fill_sub x with
                  | None -> find_possible xs
                  | x -> x
                end
              | [] -> None
            in
            let res = find_possible possible_term in
              stack := List.tl (!stack);
              res
      end
  in
    let ee = get_equiv e in
      match ee with
      | Some x -> x
      | _ -> failwith "Interpolate: unable to build middle term"

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
          let lst1 = ClpLI.interpolate_clp [And(case1::a_part); And b_part] in (*TODO incremental*)
          let lst2 = ClpLI.interpolate_clp [And(case2::a_part); And b_part] in (*TODO incremental*)
          let it = AstUtil.simplify  (Or [List.hd lst1; List.hd lst2]) in
            (A, it)
        end
        | B ->
        begin
          let (case1,case2) = neg_eq eq in
          let (a_part,b_part) = applied_to_a_b NelsonOppen.LI in
          let lst1 = ClpLI.interpolate_clp [And a_part; And (case1::b_part)] in (*TODO incremental*)
          let lst2 = ClpLI.interpolate_clp [And a_part; And (case2::b_part)] in (*TODO incremental*)
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
       (*
       try
         let m = find_middle_term common_var common_sym graph_a ea in (*need to look from b side ?*)
         let eq_a = AstUtil.order_eq (Eq(ea,m)) in
         let eq_b = AstUtil.order_eq (Eq(eb,m)) in
           [(B, eq_b);(A, eq_a)]
       with Failure "Interpolate: unable to build middle term" ->
         try 
           let m = find_middle_term common_var common_sym graph_b eb in
           let eq_a = AstUtil.order_eq (Eq(ea,m)) in
           let eq_b = AstUtil.order_eq (Eq(eb,m)) in
             [(A, eq_a);(B, eq_b)]
         with Failure "Interpolate: unable to build middle term" ->
       *)
       try
         let m = Dag.find_common_expr ea eb graph_a graph_b common_var common_sym in
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
               (*TODO bug in this part ->
                 B first => not (A |= I)
                 A first => B /\ I TODO add == for the latter interpolant
                *)
               li_flag := true; (*HACK !!!*)
               [(A, eq_a);(B, eq_b)]
               (*[(B, eq_b);(A, eq_a)]*)
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
          (*
          let eq_lst = make_deduc_local eq in
          let (side1,side2) = match eq_lst with
            | (A, eqa)::(B, eqb)::[]
            | (B, eqb)::(A, eqa)::[] ->
              begin
                match eq with
                | Eq(e1,e2) ->
                  begin
                    match ((in_eq e1 eqa),(in_eq e1 eqb),(in_eq e2 eqa),(in_eq e2 eqb)) with
                    | (false,_,_,_) -> (B,A)
                    | (_,false,_,_) -> (A,B)
                    | (_,_,false,_) -> (A,B)
                    | (_,_,_,false) -> (B,A)
                    | _ -> failwith ("Interpolate, process_deduction: sides of expressions"^(AstUtil.print eq)^" "^(AstUtil.print eqa)^" "^(AstUtil.print eqb))
                  end
                | _ -> failwith "Interpolate, process_deduction : ...(2)"
              end
            | (th, _)::[] -> (th,th)
            | _ -> failwith "Interpolate, process_deduction : ..."
          in
          *)
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
      let andAcc = ref [it] in
      let orAcc = ref [] in
        List.iter
          (fun ((side, it), eq_opt) ->
            begin
              match side with
              | A -> orAcc := it::!orAcc
              | B -> andAcc := it::!andAcc
              | Mixed -> failwith "Interpolate, recompose_final_it: mixed interpolant!"
            end;
            begin
              match eq_opt with
              | None -> ()
              | Some eq -> andAcc := eq::!andAcc (*TODO does it always work ??*)
            end
          ) partial_deduced_it;
        Or ((And !andAcc)::!orAcc)
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
