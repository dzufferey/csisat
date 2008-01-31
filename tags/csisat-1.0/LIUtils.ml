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

exception LP_SOLVER_FAILURE

type li_solver = {
    solve       : Camlglpk.t -> bool; 
    obj_val     : Camlglpk.t -> float;
    row_primal  : Camlglpk.t -> int -> float;
    rows_primal : Camlglpk.t -> int -> float array -> unit;
    row_dual    : Camlglpk.t -> int -> float;
    rows_dual   : Camlglpk.t -> int -> float array -> unit;
    col_primal  : Camlglpk.t -> int -> float;
    cols_primal : Camlglpk.t -> int -> float array -> unit;
    col_dual    : Camlglpk.t -> int -> float;
    cols_dual   : Camlglpk.t -> int -> float array -> unit
}

let simplex_wo_presolve: li_solver = {
    solve       = (fun x -> Camlglpk.simplex x true);
    obj_val     = Camlglpk.get_obj_val;
    row_primal  = Camlglpk.get_row_primal;
    rows_primal = Camlglpk.get_rows_primal;
    row_dual    = Camlglpk.get_row_dual;
    rows_dual   = Camlglpk.get_rows_dual;
    col_primal  = Camlglpk.get_col_primal;
    cols_primal = Camlglpk.get_cols_primal;
    col_dual    = Camlglpk.get_col_dual;
    cols_dual   = Camlglpk.get_cols_dual
}

let simplex: li_solver = {
    solve       = (fun x -> Camlglpk.simplex x false);
    obj_val     = Camlglpk.get_obj_val;
    row_primal  = Camlglpk.get_row_primal;
    rows_primal = Camlglpk.get_rows_primal;
    row_dual    = Camlglpk.get_row_dual;
    rows_dual   = Camlglpk.get_rows_dual;
    col_primal  = Camlglpk.get_col_primal;
    cols_primal = Camlglpk.get_cols_primal;
    col_dual    = Camlglpk.get_col_dual;
    cols_dual   = Camlglpk.get_cols_dual
}

let interior: li_solver = {
    solve       = Camlglpk.interior;
    obj_val     = Camlglpk.ipt_obj_val;
    row_primal  = Camlglpk.ipt_row_primal;
    rows_primal = Camlglpk.ipt_rows_primal;
    row_dual    = Camlglpk.ipt_row_dual;
    rows_dual   = Camlglpk.ipt_rows_dual;
    col_primal  = Camlglpk.ipt_col_primal;
    cols_primal = Camlglpk.ipt_cols_primal;
    col_dual    = Camlglpk.ipt_col_dual;
    cols_dual   = Camlglpk.ipt_cols_dual
}

let solver = ref simplex_wo_presolve

let set_solver str = match str with
  | "simplex" -> solver := simplex
  | "simplex_wo_presolve" -> solver := simplex_wo_presolve
  | "interior" -> solver := interior
  | s -> failwith (s^" is not a known LI solver")

let rec split_neq pred = match pred with
  | And lst -> And (List.map split_neq lst)
  (*| Or lst ->  Or (List.map split_neq lst)*)
  | Not (Eq(e1, e2)) -> Or [Lt(e1,e2); Lt(e2,e1)]
  | Leq _ | Lt _ | Eq _ as e -> e
  | Or _ -> failwith "split_neq: does not support 'Or'"
  | Atom _ -> failwith "split_neq: does not support 'Atom'"
  | True -> Leq(Constant 0.0, Constant 1.0)
  | False -> Leq(Constant 1.0, Constant 0.0)
  | Not _ -> failwith "split_neq: 'Not' supported onyl with 'Eq'"
  
(** extract the constant from e1 and e2
 *  return (nonCst_e1 - non_Cst_e2, Cst_e2 - Cst_e1)
 *)
let extract_constant e1 e2 =
  let rec split (accCst,accRest) expr = match expr with
    | Constant cst -> (accCst +. cst, accRest)
    | Variable _ as v -> (accCst, v::accRest)
    | Application _ as appl ->  (accCst, appl::accRest)
    | Sum lst -> List.fold_left (split) (accCst,accRest) lst
    | Coeff _ as co -> (accCst, co::accRest)
  in
  let rec negate expr = match expr with
    | Constant cst -> Constant (-. cst)
    | Variable _ as v -> Coeff(-1.0, v)
    | Application _ as appl -> Coeff(-1.0, appl)
    | Sum lst -> Sum (List.map negate lst)
    | Coeff (c, e) -> Coeff(-. c, e)
  in
    let (c1,e1) = split (0.0, []) e1 in
    let (c2,e2) = split (0.0, []) e2 in
      (simplify_expr (Sum(e1 @ (List.map negate e2))), Constant ( c2 -. c1))


(** put the constraint in the form:
 *  a_1 * x_1 + a_2 * x_2 + ... </<=/= constant
 *)
let rec to_normal_li_constraints pred = match pred with 
  | Lt (e1, e2)  -> let (s,c) = extract_constant e1 e2 in Lt(s, c)
  | Leq (e1, e2) -> let (s,c) = extract_constant e1 e2 in Leq(s, c)
  | Eq (e1, e2)  -> let (s,c) = extract_constant e1 e2 in Eq(s, c)
  (*| And lst -> And (List.map to_normal_li_constraints lst)*)
  | And _ -> failwith "to_normal_li_constraints: does not support 'And'"
  | Or _ -> failwith "to_normal_li_constraints: does not support 'Or'"
  | Atom _ -> failwith "to_normal_li_constraints: does not support 'Atom'"
  | True -> failwith "to_normal_li_constraints: does not support 'True'"
  | False -> failwith "to_normal_li_constraints: does not support 'False'"
  | Not _ -> failwith "to_normal_li_constraints: does not support 'Not'"


(** transform a conjunction of formulae into a matrix 'A' and a vector 'a'
 *  such that A*vars </<=/= a is equivalent to the input formulae
 *)
let conj_to_matrix pred_lst vars =
  Message.print Message.Debug (lazy("conj_to_matrix for: " ^ (Utils.string_list_cat ", " (List.map print pred_lst))));
  Message.print Message.Debug (lazy("vars are: " ^ (Utils.string_list_cat ", " (List.map print_expr vars))));
  let length =  List.length pred_lst in
  let matrixA = Array.make_matrix length (List.length vars) 0.0 in
  let vectorB = Array.make length 0.0 in
  let (_, var_to_index) = List.fold_left (fun (i,xs) x -> (i+1,(x,i)::xs)) (0,[]) vars in
  let rec fill_coeff row lst = match lst with
    | x::xs ->
      begin
        let _ = match x with
          | Variable _ as v ->
            let index = List.assoc v var_to_index in
              matrixA.(row).(index) <- 1.0
          | Application _ as a -> 
            (
            try
            let index = List.assoc a var_to_index in
              matrixA.(row).(index) <- 1.0
            with Not_found -> failwith ((print_expr a)^" not in assoc")
            )
          | Coeff (co, expr) ->
            let index = List.assoc expr var_to_index in
              matrixA.(row).(index) <- co
          | Constant 0.0 -> () (*when empty...*)
          | e -> failwith ("fill_coeff: 'Sum' and 'Constant' not supported: "^(print_expr e))
        in
          fill_coeff row xs
      end
    | [] -> ()
  in
  let rec fill_constraints row lst = match lst with
    | x::xs ->
      begin
        let cstr = to_normal_li_constraints x in
        let _ = match cstr with
          | Leq (Sum lst, Constant c) ->
            fill_coeff row lst;
            vectorB.(row) <- c
          | Leq (e , Constant c) ->
            fill_coeff row [e];
            vectorB.(row) <- c
          | Lt (Sum lst, Constant c) -> 
            fill_coeff row lst;
            vectorB.(row) <- c
          | Lt (e , Constant c) -> 
            fill_coeff row [e];
            vectorB.(row) <- c
          | Eq (Sum lst, Constant c) -> 
            fill_coeff row lst;
            vectorB.(row) <- c
          | Eq (e, Constant c) -> 
            fill_coeff row [e];
            vectorB.(row) <- c
          | p -> failwith ("fill_constraints: error -> " ^ (print p))
        in
          fill_constraints (row + 1) xs
      end
    | [] -> ()
  in
    fill_constraints 0 pred_lst;
    (matrixA,vectorB)


(** collect the terms that are "variable" for clp-algo (i.e. var + appl) *)
let collect_li_vars pred = 
  let rec process expr = match expr with
    | Constant _ -> []
    | Variable _ as v -> [v]
    | Application _ as a -> [a]
    | Sum lst -> List.fold_left (fun acc x -> (process x) @ acc ) [] lst
    | Coeff (co, expr) -> process expr
  in
  let rec process_pred pred = match pred with
    | And lst | Or lst -> List.fold_left (fun acc x -> (process_pred x) @ acc ) [] lst
    | Not pred -> process_pred pred
    | Eq(e1, e2) | Lt(e1, e2) | Leq(e1, e2) -> (process e1) @ (process e2)
    | _ -> []
  in
    OrdSet.list_to_ordSet (process_pred pred)

