(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
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
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)

let main =
  Camlpico.init ();
  Camlpico.enable_trace ();
  Camlpico.adjust 3 ;
  Camlpico.add 3 ;
  Camlpico.add 0 ;
  Camlpico.add 1 ;
  Camlpico.add 0 ;
  Camlpico.add 2 ;
  Camlpico.add 0 ;
  Camlpico.add (-1) ;
  Camlpico.add (-2) ;
  Camlpico.add 0 ;
  let result = Camlpico.sat (-1) in
    if result = Camlpico.satisfiable() then print_endline "sat"
    else if result = Camlpico.unsatisfiable() then print_endline "unsat"
    else if result = Camlpico.unknown() then print_endline "unk";
    print_endline (string_of_int (Camlpico.corelit 1));
    print_endline (string_of_int (Camlpico.corelit 2));
    print_endline (string_of_int (Camlpico.corelit 3))

