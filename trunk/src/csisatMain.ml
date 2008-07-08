(*  CSIsat: interpolation procedure for LA + EUF
 *  Copyright (C) 2008  The CSIsat team
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
 *)

open   CsisatAst
(**/**)
module Message     = CsisatMessage
module Config      = CsisatConfig
module AstUtil     = CsisatAstUtil
module Utils       = CsisatUtils
module OrdSet      = CsisatOrdSet
module SatPL       = CsisatSatPL
module LIUtils     = CsisatLIUtils
module NelsonOppen = CsisatNelsonOppen
module Interpolate = CsisatInterpolate
module FociPrinter = CsisatFociPrinter
module FociParse   = CsisatFociParse
module FociLex     = CsisatFociLex
module InfixLex    = CsisatInfixLex
module InfixParse  = CsisatInfixParse
(**/**)

let print_fct = ref FociPrinter.print_foci

let read_input () =
    match !(Config.syntax) with
    | Config.SyntaxUnk ->
      begin
        let buffer = Buffer.create 10000 in
          try
            while true do
              let line = read_line () in
                Buffer.add_string buffer line
            done;
            failwith "read_input: no EOF ??"
          with _ -> (*EOF*)
            begin
              try
                let lexbuf = Lexing.from_string (Buffer.contents buffer) in
                  print_fct := FociPrinter.print_foci;
                  FociParse.main FociLex.token lexbuf
              with Parsing.Parse_error ->
                begin
                  let lexbuf = Lexing.from_string (Buffer.contents buffer) in
                    print_fct := AstUtil.print_infix;
                    InfixParse.main InfixLex.token lexbuf
                end
            end
      end
    | Config.SyntaxFoci ->
      begin
        let lexbuf = Lexing.from_channel stdin in
          print_fct := FociPrinter.print_foci;
          FociParse.main FociLex.token lexbuf
      end
    | Config.SyntaxInfix ->
      begin
        let lexbuf = Lexing.from_channel stdin in
          print_fct := AstUtil.print_infix;
          InfixParse.main InfixLex.token lexbuf
      end


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
  let lst =
    if (!Config.integer_heuristics) then List.map AstUtil.integer_heuristic  lst
    else lst
  in
  let it a b = 
    try
      let it =
        if !(Config.round) then AstUtil.simplify (LIUtils.round_coeff (Interpolate.interpolate_with_proof a b))
        else Interpolate.interpolate_with_proof a b
      in
        Message.print Message.Normal (lazy(!print_fct [it]));
        if !(Config.check) then interpolant_test it a b
    with SAT_FORMULA f ->
        Message.print Message.Error (lazy("Satisfiable: "^(!print_fct [f])))
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
                if !(Config.round) then
                  List.map
                    (fun x -> AstUtil.simplify ( LIUtils.round_coeff x))
                    (Interpolate.interpolate_with_one_proof lst)
                else Interpolate.interpolate_with_one_proof lst 
              in
                List.iter (fun it ->
                  Message.print Message.Normal (lazy(!print_fct [it]));
                ) its;
                if !(Config.check) then interpolant_test_lst its lst
            with SAT_FORMULA f ->
              Message.print Message.Error (lazy("Satisfiable: "^(!print_fct [f])))
          end
      end

let sat_only () =
  let lst = read_input () in
  let lst =
    if (!Config.integer_heuristics) then List.map AstUtil.integer_heuristic  lst
    else lst
  in
  let formula = AstUtil.simplify (And lst) in
  let ans =
    (*catch the trivial cases because NelsonOppen expect no trivial formula*)
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