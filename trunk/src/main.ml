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

let interpolate_eq () =
  let tests = [
      "& [ = a b = c d ~= a e ]; & [ = b c = d e ]";
      "& [ = a b = c d = a e ]; & [ = b c = d e ~= b e]";
      "& [ = a b ]; & [ ~= a b ]";
      "& [ ~= a b ]; & [ = a b ]"
    ]
  in
    List.iter ( fun str ->
        let lst = FociParser.parse_foci str in
        let a = List.hd lst in
        let b = List.hd (List.tl lst) in
        let it = Dag.interpolate_eq a b in
          Message.print Message.Normal (lazy("is: "^(AstUtil.print it)));
          if (SatPL.is_sat (And[ a ; Not it])) then Message.print Message.Error (lazy "FAILURE: A |= I");
          if (SatPL.is_sat (And[ it ; b])) then Message.print Message.Error (lazy "FAILURE: I /\\ B")
      ) tests

let test_unsat_core () =
  let t1 = Eq( Application( "f", [ Application( "f", [Application( "f", [ Application( "f", [ Application( "f", [Variable "a"])])])])]), Variable "a") in
  let t2 = Eq( Application( "f", [ Application( "f", [ Application( "f", [Variable "a"])])]), Variable "a") in
  let t3 = Not( Eq ( Application ("f", [Variable "a"]), Variable "a")) in
  let t4 = ( Eq ( Variable "a", Variable "a")) in
  let f = And [t1;t2;t3;t4] in
  let core = NelsonOppen.unsat_core_for_convex_theory SatUIF.is_uif_sat f in
    Message.print Message.Normal (lazy("formula is "^(AstUtil.print f)));
    Message.print Message.Normal (lazy("unsat core is "^(AstUtil.print core)))

let test_split () =
  let t1 = Leq (Constant 1.0, Variable "x") in
  let t2 = Leq (Variable "x", Constant 2.0) in
  let t3 = Not (Eq (Application ("f",[Variable "x"]) , Application ("f",[Constant 1.0]))) in
  let t4 = Not (Eq (Application ("f",[Variable "x"]) , Application ("f",[Constant 2.0]))) in
  let f1 = And [t1;t2;t3;t4] in
  let t5 = Eq (Application ("f",[Variable "x"]) , Sum [Variable "x"; Variable "y"]) in
  let t6 = Leq (Variable "x", Sum [Variable "y"; Variable "z"]) in
  let t7 = Leq (Sum [Variable "x"; Variable "z"], Variable "y") in
  let t8 = Eq (Variable "y", Constant 1.0) in
  let f2 = And [t5;t6;t7;t8;t4] in
  let (uif1,li1,shared1,def1) = AstUtil.split_formula_LI_UIF f1 in
    Message.print Message.Normal (lazy("formula is "^(AstUtil.print f1)));
    Message.print Message.Normal (lazy("uif is "^(AstUtil.print (And uif1))));
    Message.print Message.Normal (lazy("li  is "^(AstUtil.print (And li1))));
    Message.print Message.Normal (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr shared1))));
    Message.print Message.Normal (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> AstUtil.print (Eq (x,y))) def1))));
  let (uif2,li2,shared2,def2) = AstUtil.split_formula_LI_UIF f2 in
    Message.print Message.Normal (lazy("formula is "^(AstUtil.print f2)));
    Message.print Message.Normal (lazy("uif is "^(AstUtil.print (And uif2))));
    Message.print Message.Normal (lazy("li  is "^(AstUtil.print (And li2))));
    Message.print Message.Normal (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr shared2))));
    Message.print Message.Normal (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> AstUtil.print (Eq (x,y))) def2))))

let test_sat_li () =
  let f1 =
    AstUtil.simplify ( List.hd (FociParser.parse_foci "& [ ~ <= 0 z  <= x z <= y x <= y 0 <= 0 + [ x y ] ]" )) in
  let f2 =
    AstUtil.simplify ( List.hd ( FociParser.parse_foci "& [  <= z 0  <= x z <= y x <= y 0 <= 0 + [ x y ] ]" )) in
  let f3 =
    AstUtil.simplify ( List.hd ( FociParser.parse_foci "& [  <= 0 x <= 0 y  <= 2 x <= 2 y <= + [ x y ] 3 ]" )) in
  let f4 =
    AstUtil.simplify ( List.hd ( FociParser.parse_foci "& [ <= 1 + [ x y ] <= -1 + [ x * -1 y]  ]" )) in
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f1)));
    if SatLI.is_li_sat f1 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT");
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f2)));
    if SatLI.is_li_sat f2 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT");
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f3)));
    if SatLI.is_li_sat f3 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT");
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f4)));
    if SatLI.is_li_sat f4 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT")

let test_unsat_liuif () =
  (*[f(x) > 0, x = y], [f(y) =< 0] *)
  let f1 = AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ ~ <= f [ x ] 0  = x y <= f [ y ] 0 ]"
     )) in
  (*[f(a) = b+5, f(f(a)) >= b+1], [f(c) = d+4, d = b+1, f(f(c)) < b+1]*)
  let f2 = AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ = f [ a ] + [ b 5 ]  <= + [ b 1 ] f [ f [ a ] ]  = f [ c ] + [ d 4 ] = d + [ b 1 ] ~ <= + [ b 1 ] f [ f [ c] ] ]"
     )) in
  (*[f(x, z) >= 1, x = y+1, z =< a, z >= b], [f(y+1, z) =< 0, a =< z, b >= z]*)
  let f3 = List.hd (FociParser.parse_foci
          "& [ <= 1 f [ x z ]  = x + [ y 1 ]  <= z a <= b z  <= f [ + [ y 1 ] z ] 0 <= a z <= z b ]"
     ) in
  (*[f(x, z) >= 1, x = y+1, z = a, z = b], [f(y+1, z) =< 0, ]*)
  let f4 = List.hd (FociParser.parse_foci
          "& [ <= 1 f [ x z ]  = x + [ y 1 ]  = z a = b z  <= f [ + [ y 1 ] z ] 0 ]"
     ) in
  (*[a =< b, a >= c, f(a) =< 1], [b =< d, c >= d, f(d) >= 2]*)
  let f5 = List.hd (FociParser.parse_foci
          "& [ <= a b  <= c a <= f [ a ] 1 <= b d <= d c <= 2 f [ d ] ]"
     ) in
  (*[f(x) >= 1], [f(y) =< -1, x =< y, x >= y]*)
  let f6 = List.hd (FociParser.parse_foci
          "& [ <= 1 f [ x ]  <= f [ y ] -1 <= y x <= x y ]"
     ) in
  (*[f(x) = 0, f(y) = 1], [x = y]*)
  let f7 = List.hd (FociParser.parse_foci
          "& [ = f [ x ] 0 = f [ y ] 1 = x y ]"
     ) in
  (*[f(x+a)=p, f(y+b) = q, a = b, p-q+z = 1], [x = y, z = 0]*)
  let f8 = List.hd (FociParser.parse_foci
          "& [ = p f [ + [ x a ] ] = q f [ + [ y b ] ] = a b = 1 + [ p * -1 q z ] = x y = z 0 ]"
     ) in
  (*[f(x+a) = p, f(y+b) = q, a = b, f(p+c) = s, f(q+d) = t, c = d, s-t+z = 1], [x = y, z = 0]*)
  let f9 = List.hd (FociParser.parse_foci
          "& [ = p f [ + [ x a ] ] = q f [ + [ y b ] ] = a b = s f [ + [ p c ] ] = t f [ + [ q d ] ] = c d = 1 + [ s * -1 t z ] = x y = z 0 ]"
     ) in
  (*[x = y], [f(x) = 1, f(a) = 0, y = a]*)
  let f10 = List.hd (FociParser.parse_foci
          "& [ = x y = f [ x ] 1 = f [ a ] 0 = y a ]"
     ) in
  (*[x =< p, x >= q, f(x) = 0], [p =< y, q >= y, f(y) = 1]*)
  let f11 = List.hd (FociParser.parse_foci
          "& [ <= x p <= q x = f [ x ] 0 <= p y <= y q = f [ y ] 1 ]"
     ) in
  let f12 = AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ = g[a] + [ c 5 ] <= + [ c 1 ] f [ g [ a ] ] = h [ b ] + [ d 4 ] = d + [ c 1 ] ~<= + [ c 1 ] f [ h [ b ] ] ]"
     )) in
  let test f =
    Message.print Message.Normal (lazy("sat li+uif for: "^(AstUtil.print f)));
    if NelsonOppen.is_liuif_sat f then Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT")
  in
   List.iter test [f1;f2;f3;f4;f5;f6;f7;f8;f9;f10;f11;f12]

let test_implied () =
  let f1 = AstUtil.simplify ( List.hd (FociParser.parse_foci
          "& [ <= x y  <= y x ]"
     )) in
    if SatLI.is_eq_implied f1 (Eq (Variable "x", Variable "y")) then
         Message.print Message.Normal (lazy "OK")
    else Message.print Message.Normal (lazy "ERROR");
  let f2 = AstUtil.simplify ( List.hd (FociParser.parse_foci
          "& [ <= z y  <= y x ]"
     )) in
    if SatLI.is_eq_implied f2 (Eq (Variable "x", Variable "y")) then
         Message.print Message.Normal (lazy "OK")
    else Message.print Message.Normal (lazy "ERROR")

let test_bool_t () =
  let f1 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ = f [ a ] + [ b 5 ]  <= + [ b 1 ] f [ f [ a ] ]  = f [ c ] + [ d 4 ] = d + [ b 1 ] ~ <= + [ b 1 ] f [ f [ c] ] ]"
     ))) in
  let f2 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ | [ = x 2 ~= y 1 ] | [ = y 1 ~= x 2 ] ~<= x 2 ]"
     ))) in
  let test f =
    Message.print Message.Normal (lazy("sat PL for: "^(AstUtil.print f)));
    if SatPL.is_sat f then Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT")
  in
    test f1;
    test f2

let test_unsat_core_with_pl () =
  let f1 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ = f [ a ] + [ b 5 ]  <= + [ b 1 ] f [ f [ a ] ]  = f [ c ] + [ d 4 ] = d + [ b 1 ] ~ <= + [ b 1 ] f [ f [ c] ] ]"
     ))) in
  let f2 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ | [ = x 2 = 1 2 ]  ~<= x 2 ]"
     ))) in
  let f3 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ = x y ~= f [x] f [y] ]"
     ))) in
  let f4 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ | [ = x 2 = 1 2 ]  ~= x 2 ]"
     ))) in
  let f5 = AstUtil.cnf (AstUtil.simplify (List.hd (FociParser.parse_foci
          "& [ | [ = x 2 = y 2 ]  ~= x 1 = x 1 ]"
     ))) in
  let print_core (core,th,eq) =
    let print_dedeq (th,eq) =
      match th with
      | NelsonOppen.LI -> "LI "^(AstUtil.print eq)
      | NelsonOppen.BOOL -> "BOOL!! "
      | NelsonOppen.UIF -> "UIF "^(AstUtil.print eq)
      | NelsonOppen.SATISFIABLE ->"NelsonOppen.SATISFIABLE!!!"
    in
    Message.print Message.Normal (lazy ("core:"^(AstUtil.print core)));
    begin
      match th with
      | NelsonOppen.LI -> Message.print Message.Normal (lazy "LI contradiction")
      | NelsonOppen.BOOL -> Message.print Message.Normal (lazy "SAT contradiction")
      | NelsonOppen.UIF -> Message.print Message.Normal (lazy "UIF contradiction")
      | NelsonOppen.SATISFIABLE -> Message.print Message.Error (lazy "NelsonOppen.SATISFIABLE!!!")
    end;
    Message.print Message.Normal (lazy("congruence is: "^(Utils.string_list_cat ", " (List.map print_dedeq eq))))
  in
  let test f =
    Message.print Message.Normal (lazy("unsat cores of "^(AstUtil.print f)));
    try 
      let cores = SatPL.unsat_cores_LIUIF f in
        List.iter print_core cores
    with SAT -> Message.print Message.Error (lazy "SAT!!!")
  in
    List.iter test [f1;f2;f3;f4;f5]

let interpolate_and_test a b =
  try
    Message.print Message.Debug (lazy("interpolant for "^(AstUtil.print a)^" and "^(AstUtil.print b)));
    let it = Interpolate.interpolate a b in
      Message.print Message.Normal (lazy(FociPrinter.print_foci [it]));
      if (SatPL.is_sat (AstUtil.simplify (And[ a ; Not it]))) then Message.print Message.Error (lazy "FAILURE: A |= I");
      if (SatPL.is_sat (AstUtil.simplify (And[ it ; b]))) then Message.print Message.Error (lazy "FAILURE: I /\\ B")
  with SAT_FORMULA f ->
    Message.print Message.Error (lazy("Satisfiable: "^(FociPrinter.print_foci [f])))

(*CLP examples
  [f(x) > 0, x = y], [f(y) =< 0]
  [f(a) = b+5, f(f(a)) >= b+1], [f(c) = d+4, d = b+1, f(f(c)) < b+1]
  [f(x, z) >= 1, x = y+1, z =< a, z >= b], [f(y+1, z) =< 0, a =< z, b >= z]
  [f(a) = b+5, f(f(a)) >= b+1], [f(c) = d+4, d = b+1, f(f(c)) < b+1]
  [a =< b, a >= c, f(a) =< 1], [b =< d, c >= d, f(d) >= 2]
  [f(x) >= 1], [f(y) =< -1, x =< y, x >= y]
  [f(x, z) >= 1, x = y+1, z =< a, z >= b], [f(y+1, z) =< 0, a =< z, b >= z]
  [x = y], [f(x) = 0, f(y) = 1]
  [f(x) = 0, f(y) = 1], [x = y]
  [x = y, z = 0], [f(x+a) = p, f(y+b) = q, a = b, p-q+z = 1]
  [f(x+a)=p, f(y+b) = q, a = b, p-q+z = 1], [x = y, z = 0]
  [x = y, z = 0], [f(x+a) = p, f(y+b) = q, a = b, f(p+c) = s, f(q+d) = t, c = d, s-t+z = 1]
  [f(x+a) = p, f(y+b) = q, a = b, f(p+c) = s, f(q+d) = t, c = d, s-t+z = 1], [x = y, z = 0]
  [x = y], [f(x) = 1, f(a) = 0, y = a]
  [x =< p, x >= q, f(x) = 0], [p =< y, q >= y, f(y) = 1]
 *)

let test_find_common_li () =
  let f1 = AstUtil.simplify ( List.hd (FociParser.parse_foci
          "& [ <= 0 + [ y * -1 x 1 ]  <= + [y 1] x ]"
     )) in
  let common = SatLI.find_common_expr f1 (Variable "x") [Variable "y"] [] in
    Message.print Message.Normal (lazy("common is: "^(AstUtil.print_expr common)))

let test_unsat_EUF () =
  let f = AstUtil.simplify ( List.hd (FociParser.parse_foci
      "& [ ~= f2[c_5] f2[c_6] = c_0 f1[c_3 c_0] = c_1 f1[c_0 c_3]  = f1[c_0 c_3] f1[c_3 c_0] = c_1 f1[c_0 c_4] = c_5 f1[c_4 c_0]  = f1[c_0 c_4] f1[c_4 c_0] = c_0 f1[c_6 c_0] = c_6 f1[c_6 c_1] ]"
     )) in
   assert (not (SatUIF.is_uif_sat f))

let interpolate_test () =
  let clp_tests = [
    (*EUQ tests*)
    "& [ = a f[f[f[a]]] = a f[f[f[f[f[a]]]]] ]; & [ ~= a f [a] ]";
    "& [ = a f[f[f[a]]] ~= a f [a] ]; &[ = a f[f[f[f[f[a]]]]] ]";
    "& [ = a f[f[f[f[f[a]]]]] ~= a f[a] ]; &[ = a f[f[f[a]]] ]";
    "& [~= a f[a] ]; &[ = a f[f[f[f[f[a]]]]] = a f[f[f[a]]] ]";
    "& [ = a f[f[f[a]]]]; & [  = a f[f[f[f[f[a]]]]] ~= a f [a] ]";
    "& [ = a f[f[f[f[f[a]]]]]]; & [  = a f[f[f[a]]] ~= a f [a] ]";
    (*LA + EUQ*)
    "& [ ~= x 1 ]; & [ = x 1]";
    "& [ ~<= f [x] 0 = x y ]; & [ <= f [y] 0 ]";
    "& [ ~= f [x] 0 = x y ]; & [ = f [y] 0 ]";
    "& [ = a b = c d ~= a e ]; & [ = b c = d e ]";
    "& [ = a b = c d ~= f[a] f[e] ]; & [ = b c = d e ]";
    "& [ = f [ a ] + [ b 5 ]  <= + [ b 1 ] f [ f [ a ] ]]; &[ = f [ c ] + [ d 4 ] = d + [ b 1 ] ~ <= + [ b 1 ] f [ f [ c] ] ]";
    "& [ <= 1 f [ x z ]  = x + [ y 1 ]  <= z a <= b z]; &[ <= f [ + [ y 1 ] z ] 0 <= a z <= z b ]";
    "& [ <= 1 f [ x z ]  = x + [ y 1 ]  = z a = b z]; &[  <= f [ + [ y 1 ] z ] 0 ]";
    "& [ = g[a] + [ c 5 ] <= + [ c 1 ] f [ g [ a ] ]]; &[ = h [ b ] + [ d 4 ] = d + [ c 1 ] ~<= + [ c 1 ] f [ h [ b ] ] ]";
    "& [ = x y]; &[ = f [ x ] 1 = f [ a ] 0 = y a ]";
    "& [ <= 1 f [ x ]]; &[  <= f [ y ] -1 <= y x <= x y ]";
    "& [ = p f [ + [ x a ] ] = q f [ + [ y b ] ] = a b = 1 + [ p * -1 q z ]]; &[ = x y = z 0 ]";
    "& [ = p f [ + [ x a ] ] = q f [ + [ y b ] ] = a b = s f [ + [ p c ] ] = t f [ + [ q d ] ] = c d = 1 + [ s * -1 t z ]]; &[ = x y = z 0 ]";
    "& [ = f [ x ] 0 = f [ y ] 1]; & [ = x y ]";
    "& [ <= x p <= q x = f [ x ] 0]; &[ <= p y <= y q = f [ y ] 1 ]";
    "& [ <= a b  <= c a <= f [ a ] 1]; &[ <= b d <= d c <= 2 f [ d ] ]"
    ]
  in
  let test str =
    let lst = FociParser.parse_foci str in
    let a = List.hd lst in
    let b = List.hd (List.tl lst) in
      Message.print Message.Normal (lazy("interpolant for "^(AstUtil.print a)^" and "^(AstUtil.print b)));
      interpolate_and_test a b
  in
    List.iter test clp_tests

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

let interpolate_in () =
  let lst = read_input () in
  let a = List.hd lst in
  let b = List.hd (List.tl lst) in
    if !(Config.check) then
      interpolate_and_test a b
    else 
      try
        let it = Interpolate.interpolate a b in
          Message.print Message.Normal (lazy(FociPrinter.print_foci [it]))
      with SAT_FORMULA f ->
        Message.print Message.Error (lazy("Satisfiable: "^(FociPrinter.print_foci [f])))
    
let sat_only () =
  let formula = AstUtil.simplify (And (read_input ())) in
  let ans = if AstUtil.is_conj_only formula then
     NelsonOppen.is_liuif_sat formula
    else
     SatPL.is_sat formula
  in
    if ans then
      Message.print Message.Normal (lazy "satisfiable")
    else
      Message.print Message.Normal  (lazy "unsatisfiable")

(*
let unsat_core_uif =
  let f = List.hd (FociParser.parse_foci
          "& [ = a b  = c a = f [ a ] _1 = d c = _2 f [ d ] ~= _1 _2 ]"
     ) in
      Message.print Message.Normal (lazy("core for "^(AstUtil.print f)^" is "^(AstUtil.print (SatUIF.unsat_core f))))
let unsat_core_uif =
  let f = List.hd (FociParser.parse_foci
          "& [ = a b  = c a = f [ a ] 1 = d c = 2 f [ d ] ]"
     ) in
      Message.print Message.Normal (lazy("core for "^(AstUtil.print f)^" is "^(AstUtil.print (NelsonOppen.unsat_core f))))
*)

let main =
  if !(Config.sat_only) then
    sat_only ()
  else
    interpolate_in ()
