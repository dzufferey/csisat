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

(*****************************************************************************)
(*************************        PRINTER         ****************************)
(*****************************************************************************)

let rec print_foci_expression exp = match exp with
    Constant cst -> (string_of_float cst) ^ " "
  | Variable var -> var ^ " "
  | Application (f, args) ->
    begin
      let args_string = List.fold_left (fun acc x -> acc ^ (print_foci_expression x) ) "" args
      in f ^ " [ " ^ args_string ^ "] "
    end
  | Sum elements ->
    begin
      let el_string = List.fold_left (fun acc x -> acc ^ (print_foci_expression x) ) "" elements
      in "+ [ " ^ el_string ^ "] "
    end
  | Coeff (cst, expr) ->
    begin
      "* " ^ (string_of_float cst) ^ " " ^ (print_foci_expression expr)
    end

let rec print_foci_predicate pred = match pred with
    True  -> "true "
  | False -> "false "
  | And pred_lst ->
    let preds_string = List.fold_left (fun acc x -> acc ^ (print_foci_predicate x) ) "" pred_lst
    in "& [ " ^ preds_string ^ "] "
  | Or pred_lst ->
    let preds_string = List.fold_left (fun acc x -> acc ^ (print_foci_predicate x) ) "" pred_lst
    in "| [ " ^ preds_string ^ "] "
  | Not pred1 -> "~ " ^ (print_foci_predicate pred1)
  | Eq (exp1, exp2) -> "= " ^ (print_foci_expression exp1) ^ (print_foci_expression exp2)
  | Lt (exp1, exp2) -> "~<= " ^ (print_foci_expression exp2) ^ (print_foci_expression exp1)
  | Leq (exp1, exp2) -> "<= " ^ (print_foci_expression exp1) ^ (print_foci_expression exp2)
  | Atom i -> "atom"^(string_of_int i)^" "

let rec print_foci pred_lst =
  let buffer = Buffer.create 0 in
    List.iter
      (fun x ->
        Buffer.add_string buffer ((print_foci_predicate x) ^ "; " )
      ) pred_lst;
    (*remove the trailling "; "*)
    Buffer.sub buffer 0 ((Buffer.length buffer) -3)

