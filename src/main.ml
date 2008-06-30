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

let read_input () =
  let buffer = Buffer.create 10000 in
    try
      while true do
        let line = read_line () in
          Buffer.add_string buffer line
      done;
      [True]
    with _ -> (*EOF*)
      FociParser.parse_foci (Buffer.contents buffer)

let interpolant_test it a b =
  if (SatPL.is_sat (AstUtil.simplify (And[ a ; Not it]))) then Message.print Message.Error (lazy "FAILURE: A |= I");
  if (SatPL.is_sat (AstUtil.simplify (And[ it ; b]))) then Message.print Message.Error (lazy "FAILURE: I /\\ B");
  let a_vars = AstUtil.get_var a in
  let b_vars = AstUtil.get_var b in
  let common_vars = OrdSet.intersection a_vars b_vars in
  let it_vars = AstUtil.get_var it in
  let diff_var = OrdSet.subtract it_vars common_vars in
    if diff_var <> [] then
      Message.print Message.Error (lazy ("FAILURE NOT COMMON VARS: "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr diff_var))));
    let a_sym = AstUtil.get_fct_sym a in
    let b_sym = AstUtil.get_fct_sym b in
    let it_sym = AstUtil.get_fct_sym it in
    let common_sym = OrdSet.intersection a_sym b_sym in
    let diff_sym = OrdSet.subtract it_sym common_sym in
      if diff_sym <> [] then
        Message.print Message.Error (lazy ("FAILURE NOT COMMON FCT SYMBOLS: "^(Utils.string_list_cat ", " diff_sym)))

let interpolant_test_lst it_lst f_lst =
  let rec mk_queries acc_q acc_a it_lst lst = match (it_lst, lst) with
    | ([],[x]) -> List.rev acc_q
    | (it::its,x::xs) ->
      begin
        let acc_a = AstUtil.normalize_only (And [x;acc_a]) in
        let b =  AstUtil.normalize_only (And xs) in
          mk_queries ((it,acc_a,b)::acc_q) acc_a its xs
      end
    | (_,_) -> failwith "Interpolate: building queries"
  in
  let queries = mk_queries [] True it_lst f_lst in
    List.iter (fun (it,a,b) -> interpolant_test it a b) queries


let interpolate_in () =
  let lst = read_input () in
  let it a b = 
    try
      (*let it = Interpolate.interpolate a b in *)
      let it =
        if !(Config.round) then LIUtils.round_coeff (Interpolate.interpolate_with_proof a b)
        else Interpolate.interpolate_with_proof a b
      in
        Message.print Message.Normal (lazy(FociPrinter.print_foci [it]));
        if !(Config.check) then interpolant_test it a b
    with SAT_FORMULA f ->
        Message.print Message.Error (lazy("Satisfiable: "^(FociPrinter.print_foci [f])))
  in
    if (List.length lst) = 2 then
      begin
        (*normal case*)
        (*TODO as soon as the path interpolation code is as good as the 2 el. case, remove this part*)
        let a = List.hd lst in
        let b = List.hd (List.tl lst) in
          it a b
      end
    else
      begin
        (*path interpolant case*)
        if List.length lst < 2 then 
          begin
            Message.print Message.Error
              (lazy
                ("Interpolation is for 2 or more formula. Only "^
                 (string_of_int (List.length lst))^
                 " formula found."));
            Message.print Message.Error (lazy("If you only want to check satisfiability, run with option '-sat'."))
          end
        else
          begin
            try
              let its = (*Interpolate.interpolate_with_one_proof lst in*)
                if !(Config.round) then List.map LIUtils.round_coeff (Interpolate.interpolate_with_one_proof lst)
                else Interpolate.interpolate_with_one_proof lst 
              in
                List.iter (fun it ->
                  Message.print Message.Normal (lazy(FociPrinter.print_foci [it]));
                ) its;
                if !(Config.check) then interpolant_test_lst its lst
            with SAT_FORMULA f ->
              Message.print Message.Error (lazy("Satisfiable: "^(FociPrinter.print_foci [f])))
          end
      end

let sat_only () =
  let formula = AstUtil.simplify (And (read_input ())) in
  let ans =
    (*catch the trivial cases because NelsonOppen expect none trivial formula*)
    if formula = True then true
    else if formula = False then false
    else if AstUtil.is_conj_only formula then
     NelsonOppen.is_liuif_sat formula
    else
     SatPL.is_sat formula
  in
    if ans then
      Message.print Message.Normal (lazy "satisfiable")
    else
      Message.print Message.Normal  (lazy "unsatisfiable")

let stat () =
  Message.print Message.Normal (lazy("total memory allocated: "^(string_of_float (Gc.allocated_bytes ()))));
  Gc.print_stat stdout;
  Gc.full_major ();
  Gc.print_stat stdout

let main =
  Random.self_init ();
  if !(Config.sat_only) then
    sat_only ()
  else
    interpolate_in ()
