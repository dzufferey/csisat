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
(**module of satisifability for propositionnal logic*)

(**return a formula with only atoms and a map from atom to expr*)
let to_sat_ast pred = 
  let dico = Hashtbl.create 23 in
  let pred_to_atom = Hashtbl.create 23 in
  let counter = ref 0 in
  let get_rep p =
    try Hashtbl.find pred_to_atom p
    with Not_found ->
      begin
        counter := 1 + !counter;
        let atom = Atom !counter in
          Hashtbl.replace dico atom p;
          Hashtbl.replace pred_to_atom p atom;
          atom
      end
  in
  let rec process pred = match pred with
    | False -> False
    | True -> True
    | Eq _ as eq -> get_rep eq
    | Lt _ as lt -> get_rep lt
    | Leq _ as leq -> get_rep leq
    | Atom _ as a -> a
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not p -> Not (process p)
  in
    (dico, process pred)

let rec nnf_to_eq_lt pred = match pred with
  | False -> False
  | True -> True
  | Eq _ as eq -> eq
  | Lt _ as lt -> lt
  | Leq (e1, e2) -> Not (Lt (e2, e2))
  | Atom _ as a -> a
  | And lst -> And (List.map nnf_to_eq_lt lst)
  | Or lst -> Or (List.map nnf_to_eq_lt lst)
  | Not p -> Not p(*if formula is in nnf, then not simplification nedded*)

let is_in_cnf f = match f with
  | And lst ->
    List.for_all (fun x -> match x with 
      | Or lst ->
        List.for_all ( fun x -> match x with
          | And _ | Or _ | Not (And _) | Not (Or _) -> false
          | _ -> true
        ) lst
      | _ -> false
    ) lst
  | _ -> false

(**return a formula on CNF
 * and a hashtable atoms to the corresponding subterm
 * TODO (Not Lt) vs Leq
 *)
let equisatisfiable pred =
  let dico = Hashtbl.create 23 in
  let pred_to_atom = Hashtbl.create 23 in
  let counter = ref 0 in
  let get_rep p =
    try Hashtbl.find pred_to_atom p
    with Not_found ->
      begin
        counter := 1 + !counter;
        let atom = Atom !counter in
          Hashtbl.replace dico atom p;
          Hashtbl.replace pred_to_atom p atom;
          atom
      end
  in
  let rep pred = match pred with
    | True -> True
    | False -> False
    | And _ as an -> get_rep an
    | Or _ as o -> get_rep o
    | Not _ as n -> get_rep n
    | Eq _ as eq -> get_rep eq
    | Lt _ as lt -> get_rep lt
    | Leq (e1,e2) -> get_rep (Not (Lt (e2, e1)))
    | Atom _ as a -> a
  in
  let enc pred = match pred with
    | False | True | Eq _ | Lt _ | Atom _ -> True
    | And lst as pp ->
      begin
        let p = rep pp in
        let repr = List.map rep lst in
        let one_false = List.map (fun x -> Or [Not p; x]) repr in
        let neg =  List.map (fun x -> Not x) repr in
          And ((Or (p::neg))::one_false)
      end
    | Or lst as pp ->
      begin
        let p = rep pp in
        let repr = List.map rep lst in
        let one_true = List.map (fun x -> Or [Not x; p]) repr in
          And ((Or ((Not p)::repr))::one_true)
      end
    | Leq (e1,e2) as leq ->
      begin
        let outer = rep leq in
        let inner = rep (Lt (e2 ,e1)) in
          And [Or[Not outer; Not inner];Or[outer; inner]](*like Not*)
      end
    | Not p as pp ->
      begin
        let outer = rep pp in
        let inner = rep p in
          And [Or[Not outer; Not inner];Or[outer; inner]]
      end
  in
    let subterm = AstUtil.get_subterm pred in
      (dico, pred_to_atom, AstUtil.simplify (And ((rep pred)::(List.map enc subterm))))

(**
 * assume NNF
 *)
let to_atoms formula =
  let dico = Hashtbl.create 23 in
  let pred_to_atom = Hashtbl.create 23 in
  let counter = ref 0 in
  let get_rep p =
    try Hashtbl.find pred_to_atom p
    with Not_found ->
      begin
        counter := 1 + !counter;
        let atom = Atom !counter in
          Hashtbl.replace dico atom p;
          Hashtbl.replace pred_to_atom p atom;
          atom
      end
  in
  let rec process formula = match formula with
    | And lst -> And (List.map process lst)
    | Or lst -> Or (List.map process lst)
    | Not p -> Not (process p)
    | Eq _ as eq -> get_rep eq
    | Lt _ as lt ->  get_rep lt
    | Leq(e1,e2) -> process (Not (Lt(e2,e1)))
    | Atom _ as a -> a
    | _ -> failwith "TRUE or FALSE found"
  in
    (dico, pred_to_atom, process formula)


(*assume NNF*)
let rec abstract dico formula = match formula with
  | And lst -> And (List.map (abstract dico) lst)
  | Or lst -> Or (List.map (abstract dico) lst)
  | Not p -> Not (abstract dico p)
  | Eq _ as eq -> Hashtbl.find dico eq
  | Lt _ as lt ->  Hashtbl.find dico lt
  | Leq(e1,e2) -> abstract dico (Not (Lt(e2,e1)))
  | Atom _ as a -> a
  | _ -> failwith "TRUE or FALSE found"

(*returns only the 'leaves'*)
let unabstract_bool dico assign =
  let lst = Utils.map_filter (
    fun (atom, value) ->
      match Hashtbl.find dico atom with
      | And _ -> None
      | Or _ -> None
      | Not _ -> None
      | Eq _ as eq -> 
        if value then Some eq
        else Some (Not eq)
      | Lt (e1,e2) as lt -> 
        if value then Some lt
        else Some (Leq(e2,e1))
      | Leq _ -> failwith "LEQ found !!"
      | Atom _ -> failwith "Atom found !!"
      | _ -> failwith "TRUE or FALSE found"
    ) assign
  in
    And lst

let unabstract_not dico clause =
  let lst = Utils.map_filter (
    fun pred ->
      let (atom, value) = match pred with
        | Atom _ as a -> (a, true)
        | Not (Atom _ as a) -> (a, false)
        | _ -> failwith "SatPL, unabstract_not: ..."
      in
        match Hashtbl.find dico atom with
        | And _ -> None
        | Or _ -> None
        | Not _ -> None
        | Eq _ as eq -> 
          if value then Some eq
          else Some (Not eq)
        | Lt (e1,e2) as lt -> 
          if value then Some lt
          else Some (Leq(e2,e1))
        | Leq _ -> failwith "LEQ found !!"
        | Atom _ -> failwith "Atom found !!"
        | _ -> failwith "TRUE or FALSE found"
    ) clause
  in
    Or lst

let is_sat_state () =
  let res = Camlpico.sat (-1) in
  if (res = Camlpico.satisfiable()) then true
  else if (res = Camlpico.unsatisfiable()) then false
  else if (res = Camlpico.unknown()) then failwith "satPL: PicoSat said UNKNOWN"
  else failwith "satPL: does not understand what PicoSat said"

let init with_core size =
  Message.print Message.Debug (lazy "initializing Sat solver:");
  Message.print Message.Debug (lazy("  with "^(string_of_int size)^" variables"));
  Message.print Message.Debug (lazy("  unsat core: "^(string_of_bool with_core)));
  Camlpico.init ();
  if with_core then Camlpico.enable_trace ();
  Camlpico.adjust size

(*return a list of pairs -> (atom, is_true)*)
let get_sat_assign max_lit =
  let a = Array.make (max_lit + 1) (Atom 0, 0) in
    for i = 1 to max_lit do
      a.(i) <- (Atom i, Camlpico.deref i)
    done;
    Utils.map_filter
      (fun (a,i) ->
        if i = 1 then Some (a, true)
        else if i = -1 then Some (a, false)
        else if i = 0 then None
        else failwith ("SatPL, get_sat_assign: picosat told "^(string_of_int i))
      )
      (Array.to_list a)

let clauses = ref []

(*return the clauses in the unsat core*)
let get_unsat_core max_lit =
  let a = Array.make (max_lit + 1) 0 in
    for i = 1 to max_lit do
      a.(i) <- Camlpico.deref i
    done;
    let ans = ref AstUtil.PredSet.empty in
      Array.iteri (fun i used -> if used = 1 then 
        begin
          Message.print Message.Debug (lazy("Atom "^(string_of_int i)^" in unsat core "));
          ans := AstUtil.PredSet.add (Atom i) !ans;
          ans := AstUtil.PredSet.add (Not (Atom i)) !ans
        end) a;
      (*TODO filter the clauses*)
      Message.print Message.Debug (lazy("clauses is: "^(Utils.string_list_cat ", " (List.map (fun x -> AstUtil.print (Or x)) !clauses))));
      List.filter (fun x -> List.for_all (fun el -> AstUtil.PredSet.mem el !ans) x) !clauses

let add_clause pred = match pred with
  | Or lst ->
    if List.length lst > 0 then
      begin
        clauses := lst::!clauses;
        List.iter
          (fun x -> match x with
            | Atom i -> Camlpico.add i
            | Not (Atom i) -> Camlpico.add (-i)
            | e -> failwith ("satPL: add_clause expect an atom, found "^(AstUtil.print e))

          ) lst;
          Camlpico.add 0
      end
  | e -> failwith ("satPL: add_clause expect a disjunction, found "^(AstUtil.print e))

let add_formula pred = match pred with
  | And lst -> List.iter add_clause lst
  | e -> failwith ("satPL: add_clause expect a conjunction, found "^(AstUtil.print e))

let reverse formula = match formula with
  | And lst ->
    begin
      Or (
        List.map (fun x -> match x with
        | Atom _ as a -> Not a
        | Not (Atom _ as a) -> a
        | _ -> failwith "satPL: reverse expect atoms only"
        ) lst)
    end
  | e -> failwith ("satPL: reverse expect a disjunction, found"^(AstUtil.print e))

(** reset the solver and the glabal variables*)
let reset () =
  Camlpico.reset ();
  clauses := []


let is_pl_sat formula =
  let (dico, _, f)  =
    if AstUtil.is_cnf formula then
      to_atoms (AstUtil.cnf formula)
    else 
      equisatisfiable formula
  in
  let f = AstUtil.cnf (AstUtil.simplify f) in
  let nb_vars = Hashtbl.length dico in
    init false nb_vars;
    add_formula f;
    let res = is_sat_state () in
      reset ();
      res

let is_sat formula =
  Message.print Message.Debug (lazy("is_sat for"^(AstUtil.print formula)));
  match formula with
  | True -> true
  | False -> false
  | formula ->
    begin
      let (atom_to_pred, pred_to_atom, f) =
        (*if is already in cnf ...*)
        if AstUtil.is_cnf formula then
          begin
            Message.print Message.Debug (lazy("already in CNF"));
            to_atoms (AstUtil.cnf formula)
          end
        else 
          begin
            Message.print Message.Debug (lazy("not CNF, using an equisatisfiable"));
            equisatisfiable formula
          end
      in
      let f = AstUtil.cnf (AstUtil.simplify f) in
        Message.print Message.Debug (lazy("abstracted formula is "^(AstUtil.print f)));
      let nb_vars = Hashtbl.length atom_to_pred in
        init false nb_vars;
        add_formula f;
        let rec test_and_refine () =
          if is_sat_state () then
            begin
              Message.print Message.Debug (lazy "found potentially SAT assign");
              let assign = unabstract_bool atom_to_pred (get_sat_assign nb_vars) in
              try
                (*TODO config can force a theory*)
                let unsat_core = NelsonOppen.unsat_core assign in
                (*let unsat_core = NelsonOppen.unsat_core_for_convex_theory assign in*)
                  Message.print Message.Debug (lazy("unsat core is: "^(AstUtil.print unsat_core)));
                let clause = abstract pred_to_atom unsat_core in
                let contra = reverse clause in
                  add_clause contra;
                  test_and_refine ()
              with SAT | SAT_FORMULA _ ->
                begin 
                  Message.print Message.Debug (lazy("assignment is SAT: "^(AstUtil.print assign)));
                  reset ();
                  true
                end
            end
          else
            begin
              reset ();
              false
            end
        in
          test_and_refine ()
        end

(** assume the formula to be unsat
 *  assume NNF
 *  TODO Stack Overflow ...
 *)
let unsat_cores_LIUIF formula =
  let cores = ref [] in
  let (atom_to_pred, pred_to_atom, f) =
    (*if is already in cnf ...*)
    if AstUtil.is_cnf formula then
      begin
        Message.print Message.Debug (lazy("already in CNF"));
        to_atoms (AstUtil.cnf formula)
      end
    else 
      begin
        Message.print Message.Debug (lazy("not CNF, using an equisatisfiable"));
        equisatisfiable formula
      end
  in
  let f = AstUtil.cnf (AstUtil.simplify f) in
    Message.print Message.Debug (lazy("abstracted formula is "^(AstUtil.print f)));
  let nb_vars = Hashtbl.length atom_to_pred in
    init false nb_vars;
    add_formula f;
    let rec test_and_refine () =
      if is_sat_state () then
        begin
          Message.print Message.Debug (lazy "found potentially SAT assign");
          let assign = unabstract_bool atom_to_pred (get_sat_assign nb_vars) in
          (*TODO config can force a theory*)
          try
            let (unsat_core, _, _) as core_with_info = NelsonOppen.unsat_core_with_info assign in
              Message.print Message.Debug (lazy("unsat core is: "^(AstUtil.print unsat_core)));
              cores := core_with_info::!cores;
              let clause = abstract pred_to_atom unsat_core in
              let contra = reverse clause in
                add_clause contra;
                clauses := List.tl !clauses; (*pop to keep only original clauses in the stack*)
                test_and_refine ()
          with SAT -> raise (SAT_FORMULA assign)
        end
      else
        begin
          Message.print Message.Debug (lazy "No potentially SAT assign");
          (*in the "boolean" core, the contradiction should be direct if any ...*)
          (*is in CNF -> DNF -> remove element that are covered by existing unsat cores*)
          (* TODO
          let bool_core = match AstUtil.dnf (And (List.map (unabstract_not atom_to_pred) (get_unsat_core nb_vars))) with
            | Or lst -> lst
            | _ -> failwith "SatPL: DNF does not returned a Or ?!"
          *)
          (* TODO avoid DNF*)
          let bool_core = match AstUtil.dnf formula with
            | Or lst -> lst
            | _ -> failwith "SatPL: DNF does not returned a Or ?!"
          in
            List.iter (fun c -> Message.print Message.Debug (lazy("possible core: "^(AstUtil.print c)))) bool_core;
            reset ();
            (*remove the clauses covered by the already found unsat cores*)
            List.iter
              (fun x ->
                match x with
                | And lst ->
                  if not (List.exists
                      (fun (c,_,_) -> match c with
                        | And c_lst -> List.for_all (fun p -> List.mem p lst) c_lst
                        | _ -> failwith "SatPL: cores are not And ..."
                      ) !cores) then
                    begin
                      (*not covered => bool contradiction*)
                      (*detect and directly add to cores*)
                      let entailed = ref AstUtil.PredSet.empty in
                      let rec process lst = match lst with
                        | x::xs ->
                          begin
                            let contra = match x with
                              | Not (Eq _ as eq) -> eq
                              | Eq _ as eq -> Not eq
                              | Lt (e1,e2) -> Leq (e2,e1)
                              | Leq (e1,e2) -> Lt (e2, e1)
                              | _ -> failwith "SatPL: not normalized formula"
                            in
                              if AstUtil.PredSet.mem contra !entailed then
                                begin
                                  cores := (And [x;contra],NelsonOppen.BOOL, [])::!cores
                                end
                              else
                                begin
                                  entailed := AstUtil.PredSet.add x !entailed;
                                  process xs
                                end
                          end
                        | [] -> failwith "SatPL: failed to detect SAT solver contradiction"
                      in
                        process lst
                    end
                | _ -> failwith "SatPL: second layer of DNF is not And ..."
              ) bool_core;
            !cores
        end
    in
      test_and_refine ()

